import logging
from collections import defaultdict

from tatsu.walkers import NodeWalker

from parsing.string_to_ltl import unary_LTL_operators, binary_LTL_operators
from parsing.util.partitioned_update_chain import (
    build_partitioned_update_chain,
    build_update_predicate_guard_replacements,
)
from programs.program import Program
from programs.util import refine_init_values
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.update import Update
from prop_lang.mathexpr import MathExpr
from prop_lang.types.ops_and_rels import MathOps, MathRels
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    normalize_ltl,
    G,
    propagate_negations,
    implies,
    conjunct,
    X,
    neg,
    F,
    strip_mathexpr,
    atomic_predicates,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


delimiters = {";", "{", "}"}


class ToProgram(NodeWalker):
    def __init__(self):
        super().__init__()
        # TODO need to find out type of variables
        #      1. integer or bool?
        #      2. if on left of updates, then state vars, otherwise env
        self.vars: set[Variable] = set()
        self.inputs: set[Variable] = set()
        self.state_vars: set[Variable] = set()
        self.updates: dict[str, set[Update]] = defaultdict(set)
        self.vars_used_in_updates: set[Variable] = set()
        self.checks = {}
        self.bool_vars: set[Variable] = set()
        self.int_vars: set[Variable] = set()
        self.related_vars: set[tuple[Variable, Variable]] = set()

    def _is_math_op(self, op) -> bool:
        return isinstance(op, (MathOps, MathRels)) or op in {
            "+",
            "-",
            "*",
            "/",
            "<",
            ">",
            "<=",
            ">=",
            "=",
            "==",
            "!=",
        }

    def walk_BiOp(self, node: BiOp):
        if self._is_math_op(node.op):
            if node.op == "=":
                if isinstance(node.left, Value):
                    if node.left.type() == BOOLEAN:
                        self.bool_vars.update(node.right.variablesin())
                    else:
                        self.int_vars.update(node.right.variablesin())
                elif isinstance(node.right, Value):
                    if node.right.type() == BOOLEAN:
                        self.bool_vars.update(node.left.variablesin())
                    else:
                        self.int_vars.update(node.left.variablesin())
            else:
                self.int_vars.update(node.variablesin())
            for v in node.left.variablesin():
                for vv in node.right.variablesin():
                    self.related_vars.add((v, vv))
        else:
            if isinstance(node.left, Variable):
                self.bool_vars.add(node.left)
            if isinstance(node.right, Variable):
                self.bool_vars.add(node.right)
        self.walk(node.left)
        self.walk(node.right)

    def walk_UniOp(self, node: UniOp):
        if node.op == "!":
            if isinstance(node.right, Value):
                self.bool_vars.add(node.right)
            self.walk(node.right)
        else:
            self.walk(node.right)

    def walk_Variable(self, node: Variable):
        self.vars.add(node)

    def walk_MathExpr(self, node: MathExpr):
        self.walk(node.formula)

    def walk_Update(self, node: Update):
        # always add a chance to stutter
        self.state_vars.add(node.left)
        self.vars.add(node.left)
        vars_in_right = node.right.variablesin()
        self.vars.update(vars_in_right)
        self.vars_used_in_updates.update([node.left] + vars_in_right)
        stutter = Update(node.left, node.left)
        self.updates[node.left.name].add(stutter)
        # add actual update
        self.updates[node.left.name].add(node)

        for v in vars_in_right:
            self.related_vars.add((node.left, v))

        if isinstance(node.right, Value):
            if node.right.type() == BOOLEAN:
                self.bool_vars.add(node.left)
            else:
                self.int_vars.add(node.left)
        elif not isinstance(node.right, Variable) and strip_mathexpr(node.right).op in {
            "+",
            "-",
            "*",
            "/",
        }:
            self.int_vars.add(node.left)
            self.int_vars.update(node.right.variablesin())
        else:
            for v in node.right.variablesin():
                self.related_vars.add((node.left, v))

        self.walk(node.left)

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

        new_macros = macros
        changed = True
        while changed:
            changed = False
            for k, v in new_macros.items():
                new_macros[k] = v.replace_formulas(macros)
                if new_macros[k] != v:
                    changed = True
        macros = new_macros

        for node in raw_formula_nodes:
            match node[0]:
                case "assume":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            f = normalize_ltl(n.replace_formulas(macros))
                            f = propagate_negations(f)
                            assumptions.append(f)
                        else:
                            fs = [
                                propagate_negations(
                                    normalize_ltl(f.replace_formulas(macros))
                                )
                                for f in n
                                if f not in delimiters
                            ]
                            assumptions.extend(fs)
                case "always assume":
                    for n in node[2]:
                        if isinstance(n, Formula):
                            f = normalize_ltl(n.replace_formulas(macros))
                            f = propagate_negations(f)
                            assumptions.append(G(f))
                        else:
                            fs = [
                                G(normalize_ltl(f.replace_formulas(macros)))
                                for f in n
                                if f not in delimiters
                            ]
                            assumptions.extend(fs)
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
                    raise Exception(
                        "Unknown TSL section " + str(node[0]) + str(node[1])
                    )

        vars_to_preds = {v: set() for v in self.vars}
        for f in assumptions:
            self.walk(f)
            for p in atomic_predicates(f):
                for v in p.variablesin():
                    if v not in vars_to_preds.keys():
                        vars_to_preds[v] = set()
                    vars_to_preds[v].add(p)
        for f in guarantees:
            self.walk(f)
            for p in atomic_predicates(f):
                for v in p.variablesin():
                    if v not in vars_to_preds.keys():
                        vars_to_preds[v] = set()
                    vars_to_preds[v].add(p)

        self.inputs = self.vars.difference(self.state_vars)
        changed = True
        while changed:
            to_add_to_int = set()
            to_add_to_bool = set()
            changed = False
            for v1, v2 in self.related_vars:
                if v1 in self.int_vars and v2 not in self.int_vars:
                    to_add_to_int.add(v2)
                    changed = True
                elif v1 in self.bool_vars and v2 not in self.bool_vars:
                    to_add_to_bool.add(v2)
                    changed = True
                elif v1 not in self.int_vars and v2 in self.int_vars:
                    to_add_to_int.add(v1)
                    changed = True
                elif v1 not in self.bool_vars and v2 in self.bool_vars:
                    to_add_to_bool.add(v1)
                    changed = True
            self.int_vars.update(to_add_to_int)
            self.bool_vars.update(to_add_to_bool)

        if len(self.int_vars.intersection(self.bool_vars)) > 0:
            raise Exception(
                "Could not infer variable types consistently. Conflicting variables: "
                + str(self.int_vars.intersection(self.bool_vars))
            )

        for v, ps in vars_to_preds.items():
            if (
                len(ps) == 1
                and v not in self.bool_vars
                and not v in self.vars_used_in_updates
            ):
                print("Booleanised input variable " + str(v))
                new_assumptions = []
                to_replace = {list(ps)[0]: v}
                for a in assumptions:
                    new_assumptions.append(a.replace_formulas(to_replace))
                assumptions = new_assumptions
                new_guarantees = []
                for g in guarantees:
                    new_guarantees.append(g.replace_formulas(to_replace))
                guarantees = new_guarantees
                self.bool_vars.add(v)
                self.int_vars.remove(v)
                self.inputs.add(v)

        types = {v.name: BOOLEAN for v in self.bool_vars}
        types.update({v.name: INTEGER for v in self.int_vars})

        chain = build_partitioned_update_chain(
            self.updates,
            self.inputs,
            state_prefix="c_",
            selector_prefix="con_act_",
            use_curr_input_snapshots=False,
        )
        eval_state = chain.eval_state
        states = set(chain.states)
        con_t = list(chain.transitions)
        all_con_act_vars = set(chain.controller_events)
        for curr_v in chain.snapshot_state_vars:
            curr_name = str(curr_v)
            if curr_name in types:
                continue
            inp_name = curr_name[5:] if curr_name.startswith("curr_") else None
            if inp_name is not None and inp_name in types:
                types[curr_name] = types[inp_name]
        program_state_vars = sorted(
            set(self.state_vars).union(chain.snapshot_state_vars), key=lambda v: str(v)
        )

        to_replace = build_update_predicate_guard_replacements(
            assumptions + guarantees,
            chain.update_predicate_key_to_guard,
        )

        if len(states) > 1:
            assumptions = list(
                map(
                    lambda x: massage_ltl(x, Variable(eval_state), to_replace),
                    assumptions,
                )
            )
            guarantees = list(
                map(
                    lambda x: massage_ltl(x, Variable(eval_state), to_replace),
                    guarantees,
                )
            )
        else:
            assumptions = [a.replace_formulas(to_replace) for a in assumptions]
            guarantees = [g.replace_formulas(to_replace) for g in guarantees]

        formula = implies(
            conjunct_formula_set(assumptions), conjunct_formula_set(guarantees)
        )

        prog = Program(
            name,
            states,
            chain.initial_state,
            [(str(v), types[str(v)]) for v in program_state_vars],
            con_t,
            [(v, types[str(v)]) for v in self.inputs],
            [(v, BOOLEAN) for v in all_con_act_vars],
            preprocess=True,
            is_determ=True,
        )

        refine_init_values(prog, formula)
        logging.info(prog.to_prog(formula))
        print(prog.to_prog(formula))

        return prog, formula


def massage_ltl(formula: Formula, controller_state: Formula, to_replace, place=False):
    if not (unary_LTL_operators | binary_LTL_operators).intersection(
        set(formula.ops_used())
    ):
        if place:
            return BiOp(
                neg(controller_state),
                "U",
                conjunct(controller_state, formula.replace_formulas(to_replace)),
            )
        else:
            return formula.replace_formulas(to_replace)
    if isinstance(formula, BiOp):
        if formula.op in binary_LTL_operators:
            new_left = massage_ltl(formula.left, controller_state, to_replace, True)
            new_right = massage_ltl(formula.right, controller_state, to_replace, True)
            return BiOp(
                new_left,
                formula.op,
                new_right,
            )
        else:
            new_left = massage_ltl(formula.left, controller_state, to_replace, place)
            new_right = massage_ltl(formula.right, controller_state, to_replace, place)

            return BiOp(new_left, formula.op, new_right)
    elif isinstance(formula, UniOp):
        if formula.op == "G":
            new_formula = massage_ltl(
                formula.right, controller_state, to_replace, False
            )
            new_formula = BiOp(controller_state, "->", new_formula)
            return G(new_formula)
        elif formula.op == "F":
            new_formula = massage_ltl(
                formula.right, controller_state, to_replace, False
            )
            new_formula = BiOp(controller_state, "&", new_formula)
            return F(new_formula)

        if formula.op == "X":
            new_formula = massage_ltl(formula.right, controller_state, to_replace, True)
            return BiOp(
                neg(controller_state),
                "U",
                conjunct(controller_state, X(new_formula)),
            )
        else:
            new_formula = massage_ltl(
                formula.right, controller_state, to_replace, place
            )
            return UniOp(formula.op, new_formula)
    else:
        return formula
