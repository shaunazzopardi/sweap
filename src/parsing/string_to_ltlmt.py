import logging
import re
from collections import defaultdict
from itertools import product
from typing import Iterator

from tatsu.grammars import Grammar
from tatsu.tool import compile
from tatsu.walkers import NodeWalker

from parsing.string_to_program import not_a_keyword, regex_keywords
from programs.program import Program
from programs.transition import Transition
from programs.util import binary_rep
from prop_lang.biop import BiOp
from prop_lang.factory import create_mathrel
from prop_lang.formula import Formula
from prop_lang.types.values import BoolAtoms
from prop_lang.update import Update
from prop_lang.mathexpr import MathExpr
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    disjunct_formula_set,
    normalize_ltl,
    G,
    stringify_pred,
    implies,
    conjunct,
    X,
    neg,
    F,
    true,
    atomic_predicates,
    sat,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.machines.wrapped_hoa import WrappedHOA
from synthesis.synthesis import synthesize

GRAMMAR = """
    @@grammar::LTL

    start = { macros }* $ ;

    macros
        = f_macro
        | 'assume' '{' { expression [';'] }* '}'
        | 'always assume' '{' { expression [';'] }* '}'
        | 'guarantee' '{' { expression [';'] }* '}'
        | 'always guarantee' '{' { expression [';'] }* '}'
        ;

    f_macro
        = atom '=' (math_predicate | math_expression | expression | math_0) ';';

    expression
        = level_0 ('->' | '<->' | '||' | '|' | '&&' | '&') expression
        | level_0
        ;

    level_0 
        = atomic ('U' | 'W' | 'R' | 'M') level_0
        | atomic
        ;

    atomic
        = '(' @:expression ')'
        | ('!' | 'X' | 'F' | 'G') atomic
        | boolean_term
        | action
        ;

    action
        = '[' atom '<-' math_expression ']';

    boolean_term
        = 'true'
        | 'false'
        | math_predicate
        | atom
        | '!' boolean_term
        ;

    math_predicate
        = ('lt' | 'le' | 'gt' | 'ge' | 'eq' | 'neq') math_expression math_expression;


    math_expression
        = ('add' | 'sub' | 'mul') math_0 math_expression
        | math_0
        ;

    math_expression_eof
        = math_expression $ ;

    math_0
        = number
        | atom
        | '(' math_expression ')'
        ;

    atom = /_?[a-zA-Z][a-zA-Z0-9_-]*/;
    number = /[ic]m?([0-9]+|[0-9]+\\.[0-9]+)\\(\\)/;
"""

translate_ops = {
    "eq": "=",
    "neq": "!=",
    "lt": "<",
    "le": "<=",
    "gt": ">",
    "ge": ">=",
    "add": "+",
    "sub": "-",
    "mul": "-",
}

unary_operators = {"!", "-"}
unary_LTL_operators = {"G", "F", "X"}
binary_operators = {"&&", "||", "&", "|", "->", "<->"}
binary_LTL_operators = {"U", "W", "R", "M"}


def tuple_to_formula(node) -> Formula:
    if isinstance(node, str):
        if re.match("(true|false|tt|ff|TRUE|FALSE|True|False|TT|FF|m?[0-9]+)", node):
            if node[0] == "m":
                return UniOp("-", Value(node[1:]))
            return Value(node)
        else:
            return Variable(node)
    elif len(node) == 2:
        if isinstance(node[0], str) and (
            node[0] in unary_operators or node[0] in unary_LTL_operators
        ):
            return UniOp(node[0], (node[1]))
        else:
            return node
    elif len(node) == 3:
        if isinstance(node[0], str) and node[0] in translate_ops.keys():
            return create_mathrel(node[1], translate_ops[node[0]], node[2])
        elif isinstance(node[1], str) and (
            node[1] in binary_operators or node[1] in binary_LTL_operators
        ):
            return BiOp((node[0]), node[1], (node[2]))
        elif node[0] == "(" and node[2] == ")":
            return node[1]
        else:
            return node
    elif len(node) == 5 and node[2] == "<-":
        if not isinstance(node[1], Variable):
            raise Exception(
                "The left hand side of an update must be a variable: "
                + " ".join(map(str, node))
            )
        return Update((node[1]), node[3])
    else:
        return node


delimiters = {";", "{", "}"}

parser: Grammar = compile(GRAMMAR)


class Semantics:
    def _default(self, ast):
        if isinstance(ast, Formula):
            return ast
        else:
            return tuple_to_formula(ast)


def string_to_ltlmt(text: str) -> Formula:
    regex_keywords.extend(
        list(
            map(
                re.compile,
                [r"e_toggle$", r"eval$", r"q_.+"],
            )
        )
    )

    formula = parser.parse(
        text,
        semantics=Semantics(),
        comments="(\\/\\*.*?\\*\\/)",
        eol_comments="\\/\\/.*?$",
    )
    return formula


class ToProgram(NodeWalker):
    def __init__(self):
        super().__init__()
        # TODO need to find out type of variables
        #      1. integer or bool?
        #      2. if on left of updates, then state vars, otherwise env
        self.vars: set[Variable] = set()
        self.inputs: set[Variable] = set()
        self.state_vars: set[Variable] = set()
        self.updates: dict[str, set[BiOp]] = defaultdict(set)
        self.checks = {}

    def walk_BiOp(self, node: BiOp):
        self.walk(node.left)
        self.walk(node.right)

    def walk_UniOp(self, node: UniOp):
        self.walk(node.right)

    def walk_Variable(self, node: Variable):
        not_a_keyword(str(node))
        self.vars.add(Variable(node.name))

    def walk_MathExpr(self, node: MathExpr):
        self.walk(node.formula)

    def walk_Update(self, node: Update):
        # always add a chance to stutter
        self.state_vars.add(node.left)
        stutter = Update(node.left, node.left)
        self.updates[node.left.name].add(stutter)
        # add actual update
        self.updates[node.left.name].add(node)
        self.walk(node.left)
        self.walk(node.right)

    # TODO
    #   env should be able to choose partition it wants to be into, and only increment within it
    def ltlmt2prog(self, formulas, name="fromTSL"):
        # First pass to collect stuff
        assumptions = []
        guarantees = []
        macros = {}
        raw_formula_nodes = []
        for node in formulas:
            if node[1] == "=":
                macros[node[0]] = node[2]
            else:
                raw_formula_nodes.append(node)

        init_assumptions = []

        for node in raw_formula_nodes:
            match node[0]:
                case "assume":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            f = normalize_ltl(n.replace_formulas(macros))
                            assumptions.append(f)
                            init_assumptions.extend(f)
                        else:
                            fs = [
                                normalize_ltl(f.replace_formulas(macros))
                                for f in n
                                if f not in delimiters
                            ]
                            assumptions.extend(fs)
                            init_assumptions.extend(fs)
                case "always assume":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            f = normalize_ltl(n.replace_formulas(macros))
                            assumptions.append(G(f))
                            if not any(
                                o
                                for o in remove_globals(f).ops_used()
                                if o in unary_LTL_operators | binary_LTL_operators
                            ):
                                init_assumptions.append(f)
                        else:
                            fs = [
                                G(normalize_ltl(f.replace_formulas(macros)))
                                for f in n
                                if f not in delimiters
                            ]
                            assumptions.extend(fs)

                            for f in fs:
                                ff = remove_globals(f)
                                if not any(
                                    o
                                    for o in ff.ops_used()
                                    if o in unary_LTL_operators | binary_LTL_operators
                                ):
                                    init_assumptions.append(ff)
                case "guarantee":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            guarantees.append(normalize_ltl(n.replace_formulas(macros)))
                        else:
                            guarantees.extend(
                                normalize_ltl(f.replace_formulas(macros))
                                for f in n
                                if f not in delimiters
                            )
                case "always guarantee":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            guarantees.append(
                                G(normalize_ltl(n.replace_formulas(macros)))
                            )
                        else:
                            guarantees.extend(
                                G(normalize_ltl(f.replace_formulas(macros)))
                                for f in n
                                if f not in delimiters
                            )
                case _:
                    raise Exception("Unknown TSL section " + str(node[0]))

        for f in assumptions:
            self.walk(f)
        for f in guarantees:
            self.walk(f)
        self.inputs = self.vars.difference(self.state_vars)

        partitions = partition_updates(self.updates)
        f = implies(conjunct_formula_set(assumptions), conjunct_formula_set(guarantees))
        print(
            f.replace_formulas(
                lambda p: (
                    stringify_pred(p)
                    if isinstance(p, MathExpr) or isinstance(p, Update)
                    else None
                )
            )
        )

        types = infer_type_of_vars(self.updates, partitions, f)

        # TODO optimise by detecting transition formulas in guarantees that can be transformed into prog transitions
        # TODO any input var that appears only in actions that have no temporal operators only need to set once (can just ignore them and set the prog var instead)
        # TODO identify bool state preds (and if not constant, i.e. controller can set to true and false, then just turn them into controller var)

        con_t = []

        init_type_values = lambda x: (
            Value(BoolAtoms.FALSE) if types[str(x)] == BOOLEAN else Value("0")
        )

        init_values = [(str(x), types[str(x)], init_type_values(x)) for x in self.vars]

        # TODO use this init_assumptions to limit env init transitions
        if not sat(conjunct_formula_set(init_assumptions), types):
            raise Exception(
                "Unsatisfiable initial assumptions: "
                + "\n".join(map(str, init_assumptions))
            )

        env_init = Variable("env_init")
        init_values.append((str(env_init), BOOLEAN, Value(BoolAtoms.TRUE)))

        orig_end_env = Variable("end")
        env_events, binary_map = binary_rep(
            self.inputs | set(map(neg, self.inputs)) | {orig_end_env}, "env_"
        )
        env_t = []
        end_env = neg(
            disjunct_formula_set(f for v, f in binary_map.items() if v != orig_end_env)
        )

        # TODO initially the environment can set the program vars to any value
        #       can assume stuff in assume to limit
        for v, f in binary_map.items():
            if v == orig_end_env:
                continue
            elif isinstance(v, UniOp) and v.op == "!":
                if types[str(v.right)] == "boolean":
                    env_t.append(
                        Transition(
                            "e_toggle",
                            f,
                            [Update(v.right, Value(BoolAtoms.FALSE))],
                            [],
                            "e_toggle",
                        )
                    )
                else:
                    env_t.append(
                        Transition(
                            "e_toggle",
                            f,
                            [Update(v.right, BiOp(v.right, "-", Value("1")))],
                            [],
                            "e_toggle",
                        )
                    )
            else:
                if types[str(v)] == "boolean":
                    env_t.append(
                        Transition(
                            "e_toggle",
                            f,
                            [Update(v, Value(BoolAtoms.TRUE))],
                            [],
                            "e_toggle",
                        )
                    )
                else:
                    env_t.append(
                        Transition(
                            "e_toggle",
                            f,
                            [Update(v, BiOp(v, "+", Value("1")))],
                            [],
                            "e_toggle",
                        )
                    )

        con_init_events, con_init_binary_map = binary_rep(
            self.state_vars | set(map(neg, self.state_vars)) | {orig_end_env}, "env_"
        )
        con_end_env = neg(
            disjunct_formula_set(
                f for v, f in con_init_binary_map.items() if v != orig_end_env
            )
        )
        env_t_init = []
        for v, f in con_init_binary_map.items():
            if v == orig_end_env:
                t = Transition("c_init", con_end_env, [], [], "e_toggle")
            elif isinstance(v, UniOp) and v.op == "!":
                if types[str(v.right)] == "boolean":
                    t = Transition(
                        "c_init",
                        f,
                        [Update(v.right, Value(BoolAtoms.FALSE))],
                        [],
                        "c_init",
                    )
                else:
                    t = Transition(
                        "c_init",
                        f,
                        [Update(v.right, BiOp(v.right, "-", Value("1")))],
                        [],
                        "c_init",
                    )
            else:
                if types[str(v)] == "boolean":
                    t = Transition(
                        "c_init",
                        f,
                        [Update(v, Value(BoolAtoms.TRUE))],
                        [],
                        "c_init",
                    )
                else:
                    t = Transition(
                        "c_init",
                        f,
                        [Update(v, BiOp(v, "+", Value("1")))],
                        [],
                        "c_init",
                    )
            env_t_init.append(t)
        to_replace = {}
        partition_to_updates = {
            ("_".join(map(str, part))): update_combinations(
                [self.updates[v] for v in part]
            )
            for part in partitions
        }
        partition_updates_items = list(partition_to_updates.items())
        if len(partition_updates_items) > 0:
            con_act_vars_no = max(len(v) for v in partition_to_updates.values())
            con_act_vars, binary_map = binary_rep(
                [Variable(str(v)) for v in range(0, con_act_vars_no)], "con_act_"
            )
            con_act_f = list(binary_map.values())
            con_act_states = set()

            for j, (var, acts) in enumerate(partition_updates_items):
                to_replace_here = {}
                next_state = (
                    "eval"
                    if j == len(partition_updates_items) - 1
                    else "c_" + str(partition_updates_items[j + 1][0])
                )
                state = "c_" + str(var)
                if j == 0:
                    env_t.append(
                        Transition(
                            "e_toggle",
                            conjunct(neg(env_init), end_env),
                            [],
                            [],
                            state,
                        )
                    )
                con_act_states.add(state)
                used_fs = []
                for i, act in enumerate(acts):
                    if i == len(acts) - 1:
                        act_bool_f = neg(disjunct_formula_set(used_fs))
                    else:
                        act_bool_f = con_act_f[i]
                        used_fs.append(act_bool_f)
                    for a in act:
                        if a in to_replace_here.keys():
                            to_replace_here[a].append(act_bool_f)
                        else:
                            to_replace_here[a] = [act_bool_f]
                    con_t.append(
                        Transition(
                            state,
                            act_bool_f,
                            list(act),
                            [],
                            next_state,
                        )
                    )

                for act, fs in to_replace_here.items():
                    to_replace[act] = BiOp(
                        neg(Variable(state)),
                        "U",
                        conjunct(Variable(state), disjunct_formula_set(fs)),
                    )
        else:
            con_act_states = []
            con_act_vars = []

            env_t.append(
                Transition(
                    "e_toggle",
                    conjunct(neg(env_init), end_env),
                    [],
                    [],
                    "eval",
                )
            )
        env_t.append(
            Transition(
                "eval",
                true(),
                [],
                [],
                "e_toggle",
            )
        )
        env_t_init.append(
            Transition(
                "e_toggle",
                conjunct(env_init, end_env),
                [Update(env_init, Value(BoolAtoms.FALSE))],
                [],
                "eval",
            )
        )

        assumptions = list(
            map(
                lambda x: massage_ltl(x, Variable("eval"), to_replace),
                assumptions,
            )
        )
        guarantees = list(
            map(
                lambda x: massage_ltl(x, Variable("eval"), to_replace),
                guarantees,
            )
        )

        assumptions.append(G(F(Variable("eval"))))

        formula = implies(
            conjunct_formula_set(assumptions), conjunct_formula_set(guarantees)
        )

        prog = Program(
            name,
            ["e_toggle", "c_init", "eval"] + list(con_act_states),
            "c_init",
            init_values,
            con_t + env_t + env_t_init,
            list(set(env_events + con_init_events)),
            list(con_act_vars),
            preprocess=True,
        )
        logging.info(prog.to_prog(formula))
        print(prog.to_prog(formula))

        return prog, formula


# TODO instead of adding all Us, we want to reduce the number of alternations, which requires adding U/W depending on
#   whether on the current path in the syntax tree adding this U/W would create a new alternation
#   so, at the start of the formula we need some lookahead
#   this will keep the massaged formula within the same hardness as the original one
def massage_ltl(formula: Formula, controller_state: Variable, to_replace):
    if not (unary_LTL_operators | binary_LTL_operators).intersection(
        set(formula.ops_used())
    ):
        return BiOp(
            neg(controller_state),
            "U",
            conjunct(controller_state, formula.replace_formulas(to_replace)),
        )
    if isinstance(formula, BiOp):
        new_left = massage_ltl(formula.left, controller_state, to_replace)
        new_right = massage_ltl(formula.right, controller_state, to_replace)
        if formula.op == "U":
            return BiOp(
                new_left,
                "U",
                new_right,
            )
        else:
            return BiOp(new_left, formula.op, new_right)
    elif isinstance(formula, UniOp):
        new_formula = massage_ltl(formula.right, controller_state, to_replace)
        if formula.op == "G":
            return G(new_formula)
        elif formula.op == "F":
            return F(new_formula)
        elif formula.op == "X":
            return BiOp(
                neg(controller_state),
                "U",
                conjunct(controller_state, X(new_formula)),
            )
        else:
            return UniOp(formula.op, new_formula)
    else:
        return formula


def partition_updates(updates: dict[Variable, set[BiOp]]) -> list[set[Variable]]:
    """
    Partition variables into sets of variables that should be updated together.
    :param updates: A dictionary mapping variables to their updates.
    :return: A list of sets of variables that should be updated together.
    """
    partitions = {}
    others = {}
    for var, ups in updates.items():
        if var not in others.keys():
            var_deps = {str(v) for u in ups for v in u.right.variablesin()}
            others[var] = {var} | var_deps
            already_in_part = set(partitions.keys()).intersection(var_deps)
            if already_in_part:
                new_part = set.union(*[partitions[v] for v in already_in_part])
                new_part = new_part.union({var})
                partitions[var] = new_part
            else:
                partitions[var] = others[var]

    return [set(map(str, p)) for p in partitions.values()]


def update_combinations(updates: Iterator[Iterator[BiOp]]):
    """
    Generate all combinations of updates from a list of update sets.
    :param updates: A list of sets of updates.
    :return: A list of all combinations of updates.
    """
    if not updates:
        return []
    return list(product(*[list(ups) for ups in updates if len(ups) > 0]))


def infer_type_of_vars(updates: dict[str, set[BiOp]], partitions, formula) -> dict:
    """
    Infer the type of variables based on their updates.
    :param updates: A dictionary mapping variables to their updates.
    :return: A string representing the type of the variables.
    """
    types = {}
    preds = atomic_predicates(formula)
    for p in preds:
        if isinstance(p, MathExpr):
            for v in p.variablesin():
                # TODO this needs to change once we support reals
                types[str(v)] = INTEGER
        else:
            for v in p.variablesin():
                types[str(v)] = BOOLEAN

    for var, ups in updates.items():
        for u in ups:
            if var not in types.keys():
                if isinstance(u.right, Value):
                    if u.right.type() == BOOLEAN:
                        types[var] = BOOLEAN
                    elif u.right.type() == INTEGER:
                        types[var] = INTEGER
                elif isinstance(u.right, MathExpr):
                    types[var] = INTEGER

            if var in types.keys():
                for v in u.right.variablesin():
                    if str(v) not in types.keys():
                        types[str(v)] = types[var]

    left = [v for v in updates.keys() if v not in types.keys()]
    for v in left:
        for p in partitions:
            if v in p:
                for vv in p:
                    if vv in types.keys():
                        types[v] = types[vv]
                        break
    left = [v for v in updates.keys() if v not in types.keys()]
    if len(left) > 0:
        raise Exception("Could not infer type of variables: " + str(left))
    return types


def remove_globals(formula: Formula) -> Formula:
    if isinstance(formula, BiOp):
        new_left = remove_globals(formula.left)
        new_right = remove_globals(formula.right)
        return BiOp(new_left, formula.op, new_right)
    elif isinstance(formula, UniOp):
        new_formula = remove_globals(formula.right)
        if formula.op == "G":
            return new_formula
        else:
            return UniOp(formula.op, new_formula)
    else:
        return formula


# TODO HEURISTIC:
#   get invariants of (from assume/ always assume)
#         if there is an input that is assumed to have a finite amount of values
#           then

# TODO for inputs, get all preds
#       instead of incrementing and decrementing
#

# TODO env events sho

# TODO Optimisations:
#   for v in self.state_vara:
#       if there are no increments and decrements, then disable fairness for them.
#       can also just booleanise, unless var used in updates or predicates with +/- (MathOps, make sure to use MathOp when parsing expressions)

# TODO see f-real.tlsmt
#       removing [t <- ee] allows to solve problem, why?

# TODO analyse LTL formula to get initial conditions
#       look at assume, collect predicates true in first state (unnested preds; direct children of globally)
#       look at always assume, collect unnested preds, preds that are direct children of globablly
#       look at guarantees, if outside implication, do as above.
#       if any (eq x c) in these, then no need to inc/dec in e/c_init
