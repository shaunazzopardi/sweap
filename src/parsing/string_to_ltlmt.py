import logging
from collections import defaultdict
from itertools import product
from typing import Iterator

from tatsu.walkers import NodeWalker

from parsing.string_to_ltl import unary_LTL_operators, binary_LTL_operators
from programs.program import Program
from programs.transition import Transition
from programs.util import binary_rep, refine_init_values
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.update import Update
from prop_lang.mathexpr import MathExpr
from prop_lang.types.ops_and_rels import BoolBiOps, LTLBiOps, MathOps, MathRels
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.util import (
    conjunct_formula_set,
    disjunct_formula_set,
    normalize_ltl,
    G,
    propagate_negations,
    implies,
    conjunct,
    X,
    neg,
    F,
    true,
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
        self.bool_vars: set[str] = set()
        self.int_vars: set[str] = set()
        self._context_stack: list[str] = []
        self._update_edges: list[tuple[str, str]] = []

    def _push_context(self, context: str) -> None:
        self._context_stack.append(context)

    def _pop_context(self) -> None:
        if self._context_stack:
            self._context_stack.pop()

    def _current_context(self) -> str:
        if self._context_stack:
            return self._context_stack[-1]
        return "bool"

    def _mark_bool(self, name: str) -> None:
        if name not in self.int_vars:
            self.bool_vars.add(name)

    def _mark_int(self, name: str) -> None:
        self.int_vars.add(name)
        self.bool_vars.discard(name)
        self._propagate_int_from_updates()

    def _propagate_int_from_updates(self) -> None:
        changed = True
        while changed:
            changed = False
            for left, right in self._update_edges:
                if left in self.int_vars and right not in self.int_vars:
                    self.int_vars.add(right)
                    self.bool_vars.discard(right)
                    changed = True
                elif right in self.int_vars and left not in self.int_vars:
                    self.int_vars.add(left)
                    self.bool_vars.discard(left)
                    changed = True

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
            self._push_context("int")
            self.walk(node.left)
            self.walk(node.right)
            self._pop_context()
        else:
            self._push_context("bool")
            self.walk(node.left)
            self.walk(node.right)
            self._pop_context()

    def walk_UniOp(self, node: UniOp):
        if node.op == "!":
            self._push_context("bool")
            self.walk(node.right)
            self._pop_context()
        else:
            self.walk(node.right)

    def walk_Variable(self, node: Variable):
        self.vars.add(Variable(node.name))
        if self._current_context() == "int":
            self._mark_int(str(node))
        else:
            self._mark_bool(str(node))

    def walk_MathExpr(self, node: MathExpr):
        if not isinstance(node.formula, Variable):
            self._push_context("int")
        self.walk(node.formula)
        self._pop_context()

    def walk_Update(self, node: Update):
        # always add a chance to stutter
        self.state_vars.add(node.left)
        self.vars_used_in_updates.update([node.left] + node.right.variablesin())
        stutter = Update(node.left, node.left)
        self.updates[node.left.name].add(stutter)
        # add actual update
        self.updates[node.left.name].add(node)
        left_name = str(node.left)
        if isinstance(node.right, Value):
            if node.right.type() == BOOLEAN:
                self._mark_bool(left_name)
            else:
                self._mark_int(left_name)
        elif isinstance(node.right, MathExpr):
            self._mark_int(left_name)
        elif left_name in self.bool_vars:
            self._mark_bool(left_name)
        elif isinstance(node.right, Variable):
            right_name = str(node.right)
            self._update_edges.append((left_name, right_name))
            if right_name in self.int_vars:
                self._mark_int(left_name)
            elif right_name in self.bool_vars:
                self._mark_bool(left_name)

        self.walk(node.left)
        if left_name in self.int_vars:
            if isinstance(node.right, Variable):
                self._mark_int(str(node.right))
            self._push_context("int")
            self.walk(node.right)
            self._pop_context()
        else:
            if isinstance(node.right, Variable) and left_name in self.bool_vars:
                self._mark_bool(str(node.right))
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
        # TODO: to make this more complete, first normalise each predicate
        for v, ps in vars_to_preds.items():
            if (
                len(ps) == 1
                and str(v) not in self.bool_vars
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
                self.bool_vars.add(str(v))
                self.int_vars.remove(str(v))
                self.inputs.add(v)

        # TODO: for output vars that are assigned only constants,
        #       and their initial value is either ignored or also one of these constants
        #       then apply use binary encoding, and give control to controller
        #       PROBLEM: what happens if there is an assumption involving this variable?
        #       e.g. (eq q i0()) as an assumption? if we turn this into a controller var,
        #       then this will make the problem trivially unrealizable
        # for v, us in self.updates.items():
        #     if not any(
        #         u for u in us if len(u.right.variablesin()) > 0 and u.left != u.right
        #     ):
        #         print("Turning state variable into controller update " + str(v))

        partitions = partition_updates(self.updates, self.inputs)

        types = {v: BOOLEAN for v in self.bool_vars}
        types.update({v: INTEGER for v in self.int_vars})
        # TODO: when controller transitions for a certain partition/var are just two,
        #  then var could be turned into a boolean (if irrelevant for init assumptions)

        # TODO optimise by detecting transition formulas in guarantees that can be transformed into prog transitions
        # TODO any input var that appears only in actions that have no temporal operators only need to set once (can just ignore them and set the prog var instead)
        # TODO identify bool state preds (and if not constant, i.e. controller can set to true and false, then just turn them into controller var)

        eval_state = None
        con_t = []

        # TODO: need to find a better way to limit the number of controller action variables
        #       currently, if there are many partitions with many updates, this will explode
        #       update partitions are ideally chosen from separately
        #       when can we do this?
        #       problem: if done separately, input values can change between partitions, which may affect updates
        #                and also the controllability of the LTL formula, which may have conditions on inputs
        #                one solution is to store these in intermediate state vars, but then may need more predicates
        #                e.g. if we have GF(input > 0) as an assumption, the env could set this only when input not used
        #                one solution is to massage the formula such that input preds are evaluated only in
        #                partitions updates they are used in?
        #                one solution: inputs by default are state vars that keep value,
        #                and must be reset explicitly in a transition
        #                then we do not need to replicate input preds for an intermediate variable
        #                so for input preds we can only have: i := i, or i := reset, or i := *, or not present?
        #                do not expose this to user for now, just do it internally
        #                if we have this, we can do partitions separately here
        #                and in RPGs we can also then partition transitions with same src, tgt,
        #                and guard but multiple update choices
        partition_to_updates = {
            ("_".join(part)): update_combinations([self.updates[v] for v in part])
            for part in partitions
        }
        partition_updates_items = list(partition_to_updates.items())
        to_replace = {}

        states = set()
        if len(partition_updates_items) > 0:
            con_act_vars_no = max(len(v) for v in partition_to_updates.values())
            con_act_vars, binary_map = binary_rep(
                [Variable(str(v)) for v in range(0, con_act_vars_no)], "con_act_"
            )
            con_act_f = list(binary_map.values())

            for j, (var, acts) in enumerate(partition_updates_items):
                to_replace_here = {}
                last_partition = j == len(partition_updates_items) - 1

                state = "c_" + str(var)
                states.add(state)
                if not eval_state:
                    eval_state = state

                next_state = (
                    eval_state
                    if last_partition
                    else "c_" + str(partition_updates_items[j + 1][0])
                )

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
            eval_state = "eval"
            con_act_vars = []
            con_t.append(
                Transition(
                    eval_state,
                    true(),
                    [],
                    [],
                    eval_state,
                )
            )
        states.add(eval_state)
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

        formula = implies(
            conjunct_formula_set(assumptions), conjunct_formula_set(guarantees)
        )

        prog = Program(
            name,
            states,
            eval_state,
            [(str(v), types[str(v)]) for v in self.state_vars],
            con_t,
            [(v, types[str(v)]) for v in self.inputs],
            [(v, BOOLEAN) for v in con_act_vars],
            preprocess=True,
        )
        # The below is not sound, imagine an F x = 0 as the guarantee, if we set x to 0 in initial state, then
        # the program is no longer sound; this can probably be fixed, so leaving it here for now
        #
        # formula = formula.replace_formulas(
        #     {Variable(s): False for s in states if s not in prog.states}
        # )
        # initial_assumptions = remove_globals(extract_global_formula(formula.left))
        #
        # refine_init_values(prog, initial_assumptions)

        refine_init_values(prog, formula)
        logging.info(prog.to_prog(formula))
        print(prog.to_prog(formula))

        return prog, formula


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


def partition_updates(updates: dict[str, set[BiOp]], inputs) -> list[set[Variable]]:
    """
    Partition variables into sets of variables that should be updated together.
    :param updates: A dictionary mapping variables to their updates.
    :return: A list of sets of variables that should be updated together.
    """
    update_vars = set(updates.keys())
    input_names = {str(v) for v in inputs}

    # vars with at least one update that depends on an input variable should be put
    # in one partition (the first partition).
    input_dependent = set()
    for var, ups in updates.items():
        for u in ups:
            if any(str(v) in input_names for v in u.right.variablesin()):
                input_dependent.add(var)
                break

    remaining = update_vars - input_dependent
    adjacency: dict[str, set[str]] = {v: set() for v in remaining}

    # need to add updates to same partition if they depend on each other,
    #   so forall u1 in part . exists u2 . u2.left in vars(u1.right) and vice versa
    # then need to order the partitions:
    #   given two partitions A and B, if there is u1 in A and u2 in B,
    #   s.t. u2.left in vars(u1.right), then A before B
    for var in remaining:
        for u in updates.get(var, []):
            for dep_var in u.right.variablesin():
                dep = str(dep_var)
                if dep in remaining:
                    adjacency[var].add(dep)

    index = 0
    indices: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    partitions: list[set[str]] = []

    def strongconnect(node: str) -> None:
        nonlocal index
        indices[node] = index
        lowlinks[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for neighbor in adjacency.get(node, []):
            if neighbor not in indices:
                strongconnect(neighbor)
                lowlinks[node] = min(lowlinks[node], lowlinks[neighbor])
            elif neighbor in on_stack:
                lowlinks[node] = min(lowlinks[node], indices[neighbor])

        if lowlinks[node] == indices[node]:
            component = set()
            while True:
                popped = stack.pop()
                on_stack.remove(popped)
                component.add(popped)
                if popped == node:
                    break
            partitions.append(component)

    for var in sorted(remaining):
        if var not in indices:
            strongconnect(var)

    partition_index = {}
    for idx, part in enumerate(partitions):
        for var in part:
            partition_index[var] = idx

    edges: dict[int, set[int]] = {i: set() for i in range(len(partitions))}
    in_degree = {i: 0 for i in range(len(partitions))}
    for var in remaining:
        src_idx = partition_index[var]
        for u in updates.get(var, []):
            for dep_var in u.right.variablesin():
                dep = str(dep_var)
                if dep in remaining:
                    dst_idx = partition_index[dep]
                    if src_idx != dst_idx and dst_idx not in edges[src_idx]:
                        edges[src_idx].add(dst_idx)
                        in_degree[dst_idx] += 1

    ready = [i for i in range(len(partitions)) if in_degree[i] == 0]
    ordered_indices = []
    while ready:
        ready.sort(key=lambda i: sorted(partitions[i])[0])
        idx = ready.pop(0)
        ordered_indices.append(idx)
        for nxt in edges[idx]:
            in_degree[nxt] -= 1
            if in_degree[nxt] == 0:
                ready.append(nxt)

    if len(ordered_indices) != len(partitions):
        ordered_indices = list(range(len(partitions)))

    ordered = [partitions[i] for i in ordered_indices]

    if input_dependent:
        merged = set(input_dependent)
        remaining_parts = ordered
        changed = True
        while changed:
            changed = False
            next_remaining = []
            for part in remaining_parts:
                depends_on_merged = False
                for var in part:
                    for u in updates.get(var, []):
                        if any(str(v) in merged for v in u.right.variablesin()):
                            depends_on_merged = True
                            break
                    if depends_on_merged:
                        break
                if depends_on_merged:
                    merged.update(part)
                    changed = True
                else:
                    next_remaining.append(part)
            remaining_parts = next_remaining

        return [merged] + remaining_parts

    return ordered


def update_combinations(updates: Iterator[Iterator[str]]) -> list[tuple[str, ...]]:
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


def infer_var_types_with_booleans(
    state_vars: set[Variable],
    input_vars: set[Variable],
    updates: dict[str, set[Update]],
    formula: Formula,
) -> dict[str, object]:
    """Infer types with boolean context awareness for state and input variables."""

    bool_vars: set[str] = set()
    int_vars: set[str] = set()
    math_ops = {"+", "-", "*", "/", "<", ">", "<=", ">=", "=", "==", "!="}

    def mark_bool(name: str) -> None:
        if name not in int_vars:
            bool_vars.add(name)

    def mark_int(name: str) -> None:
        int_vars.add(name)
        bool_vars.discard(name)

    def is_math_op(op) -> bool:
        return isinstance(op, (MathOps, MathRels)) or op in math_ops

    def visit(node: Formula, context: str = "bool") -> None:
        if isinstance(node, Value):
            return
        if isinstance(node, Variable):
            if context == "int":
                mark_int(str(node))
            else:
                mark_bool(str(node))
            return
        if isinstance(node, MathExpr):
            for v in node.variablesin():
                mark_int(str(v))
            return
        if isinstance(node, Update):
            left_name = str(node.left)
            if isinstance(node.right, Value):
                if node.right.type() == BOOLEAN:
                    mark_bool(left_name)
                else:
                    if left_name not in bool_vars:
                        mark_int(left_name)
            else:
                if left_name in bool_vars:
                    mark_bool(left_name)
                elif isinstance(node.right, MathExpr):
                    mark_int(left_name)
            visit(node.right, "int" if left_name in int_vars else "bool")
            return
        if isinstance(node, UniOp):
            if node.op == "!":
                visit(node.right, "bool")
            else:
                visit(node.right, "bool")
            return
        if isinstance(node, BiOp):
            if is_math_op(node.op):
                visit(node.left, "int")
                visit(node.right, "int")
            elif isinstance(node.op, (BoolBiOps, LTLBiOps)) or node.op in {
                "&",
                "&&",
                "|",
                "||",
                "->",
                "<->",
                "U",
                "W",
                "R",
                "M",
            }:
                visit(node.left, "bool")
                visit(node.right, "bool")
            else:
                visit(node.left, "bool")
                visit(node.right, "bool")
            return

    visit(formula, "bool")
    for f in global_assumptions:
        visit(f, "bool")
    for updates_for_var in updates.values():
        for update in updates_for_var:
            visit(update, "bool")

    types: dict[str, object] = {}
    for name in bool_vars:
        types[name] = BOOLEAN
    for name in int_vars:
        types[name] = INTEGER

    unknown = {str(v) for v in (state_vars | input_vars)} - set(types.keys())
    if unknown:
        raise Exception("Could not infer type of variables: " + str(sorted(unknown)))

    return types


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
