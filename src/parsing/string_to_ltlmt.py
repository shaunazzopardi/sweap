import itertools
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
    should_be_math_expr,
    strip_mathexpr,
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

        # TODO: to make this more complete, first normalise each predicate
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

        types = {v.name: BOOLEAN for v in self.bool_vars}
        types.update({v.name: INTEGER for v in self.int_vars})
        # TODO: when controller transitions for a certain partition/var are just two,
        #  then var could be turned into a boolean (if irrelevant for init assumptions)

        # TODO optimise by detecting transition formulas in guarantees that can be transformed into prog transitions
        # TODO any input var that appears only in actions that have no temporal operators only need to set once (can just ignore them and set the prog var instead)
        # TODO identify bool state preds (and if not constant, i.e. controller can set to true and false, then just turn them into controller var)

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

        eval_state = None

        states = set()
        if len(partition_updates_items) > 0:
            all_con_act_vars = set()
            for j, (var, acts) in enumerate(partition_updates_items):
                con_act_vars_no = len(acts)
                con_act_vars, binary_map = binary_rep(
                    [Variable(str(v)) for v in range(0, con_act_vars_no)], "con_act_"
                )
                all_con_act_vars.update(con_act_vars)
                con_act_f = list(binary_map.values())

                to_replace_here = {}
                last_partition = j == len(partition_updates_items) - 1

                acts = sorted(acts, key=lambda x: str(x[0]))

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
                    if state != eval_state:
                        to_replace[act] = BiOp(
                            neg(Variable(state)),
                            "U",
                            conjunct(Variable(state), disjunct_formula_set(fs)),
                        )
                    else:
                        to_replace[act] = disjunct_formula_set(fs)
        else:
            eval_state = "eval"
            all_con_act_vars = []
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
        print(len(con_t))

        prog = Program(
            name,
            states,
            eval_state,
            [(str(v), types[str(v)]) for v in self.state_vars],
            con_t,
            [(v, types[str(v)]) for v in self.inputs],
            [(v, BOOLEAN) for v in all_con_act_vars],
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
        if formula.op in {"G", "F"} and not (
            unary_LTL_operators | binary_LTL_operators
        ).intersection(set(formula.right.ops_used())):
            new_formula = formula.right.replace_formulas(to_replace)
            if formula.op == "G":
                new_formula = BiOp(controller_state, "->", new_formula)
                return G(new_formula)
            elif formula.op == "F":
                new_formula = BiOp(controller_state, "&", new_formula)
                return F(new_formula)

        new_formula = massage_ltl(formula.right, controller_state, to_replace, True)
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

    remaining = update_vars
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

    # put input dependent parition first
    if input_dependent and len(ordered) > 1:
        first = None
        for i, p in enumerate(ordered):
            if input_dependent.issubset(p):
                first = i
                break
        if first:
            first_part = ordered[first]
            remaining_parts = ordered[:first] + ordered[first + 1 :]
        else:
            input_parts = {
                i: p for i, p in enumerate(ordered) if not p.isdisjoint(input_dependent)
            }
            first_part = list(
                itertools.chain.from_iterable(p for p in input_parts.values())
            )
            remaining_parts = [
                p for i, p in enumerate(ordered) if i not in input_parts.keys()
            ]
        # changed = True
        # while changed:
        #     changed = False
        #     next_remaining = []
        #     for part in remaining_parts:
        #         depends_on_merged = False
        #         for var in part:
        #             for u in updates.get(var, []):
        #                 if any(str(v) in merged for v in u.right.variablesin()):
        #                     depends_on_merged = True
        #                     break
        #             if depends_on_merged:
        #                 break
        #         if depends_on_merged:
        #             merged.update(part)
        #             changed = True
        #         else:
        #             next_remaining.append(part)
        #     remaining_parts = next_remaining

        return [first_part] + remaining_parts

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
