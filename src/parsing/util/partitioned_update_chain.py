import itertools
import logging
from dataclasses import dataclass
from itertools import product
from typing import Iterator

from analysis.smt_checker import quantifier_elimination
from pysmt.shortcuts import Exists, Not, Symbol
from pysmt.typing import BOOL, INT
from programs.binary_rep_map import BinaryRepMap
from programs.transition import Transition
from programs.util import binary_rep
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.update import Update
from prop_lang.util import (
    atomic_predicates,
    conjunct,
    disjunct_formula_set,
    fnode_to_formula,
    is_tautology,
    neg,
    put_next_vars_on_left_side,
    sat,
    simplify_formula_with_math,
    strip_mathexpr,
    true,
)
from prop_lang.variable import Variable


@dataclass
class PartitionedUpdateChain:
    states: set[str]
    initial_state: str
    eval_state: str
    transitions: list[Transition]
    controller_events: set[Variable]
    update_predicate_key_to_guard: dict[str, Formula]
    snapshot_state_vars: set[Variable]


def _canonical_update_predicate_keys(update: Update) -> list[str]:
    base_pred = BiOp(
        Variable(str(update.left) + "'"), "=", strip_mathexpr(update.right)
    )
    keys: dict[str, None] = {str(strip_mathexpr(base_pred)): None}
    try:
        _, next_left = put_next_vars_on_left_side(strip_mathexpr(base_pred))
        keys[str(strip_mathexpr(next_left))] = None
    except Exception:
        pass
    return sorted(keys.keys())


def build_update_predicate_guard_replacements(
    formulas: Formula | list[Formula],
    update_predicate_key_to_guard: dict[str, Formula],
) -> dict[Formula, Formula]:
    def _collect_update_atoms(formula: Formula) -> set[Update]:
        if isinstance(formula, Update):
            return {formula}
        if isinstance(formula, BiOp):
            return _collect_update_atoms(formula.left) | _collect_update_atoms(
                formula.right
            )
        if isinstance(formula, MathExpr):
            return _collect_update_atoms(formula.formula)
        if hasattr(formula, "right"):
            # UniOp and other unary wrappers
            return _collect_update_atoms(formula.right)
        return set()

    normalized_formulas = [formulas] if isinstance(formulas, Formula) else formulas

    to_replace: dict[Formula, Formula] = {}
    for formula in normalized_formulas:
        for atom in atomic_predicates(formula):
            key = str(strip_mathexpr(atom))
            guard = update_predicate_key_to_guard.get(key)
            if guard is None:
                continue
            to_replace[atom] = guard
            if not isinstance(atom, MathExpr):
                to_replace[MathExpr(atom)] = guard
        for upd in _collect_update_atoms(formula):
            guards = [
                update_predicate_key_to_guard[k]
                for k in _canonical_update_predicate_keys(upd)
                if k in update_predicate_key_to_guard
            ]
            if len(guards) > 0:
                to_replace[upd] = disjunct_formula_set(guards)
    return to_replace


def format_update_predicate_guard_map(
    update_predicate_key_to_guard: dict[str, Formula],
    *,
    update_predicate_key_to_guard_display: dict[str, str] | None = None,
    guard_bits: set[Variable] | None = None,
) -> str:
    if len(update_predicate_key_to_guard) == 0:
        return "Partition update predicate -> guards map: <empty>"

    pred_keys = sorted(update_predicate_key_to_guard.keys())
    table_rhs_display = {
        pred_key: (
            update_predicate_key_to_guard_display[pred_key]
            if update_predicate_key_to_guard_display is not None
            and pred_key in update_predicate_key_to_guard_display
            else str(update_predicate_key_to_guard[pred_key])
        )
        for pred_key in pred_keys
    }
    pred_to_guard_code = BinaryRepMap(
        {pred_key: update_predicate_key_to_guard[pred_key] for pred_key in pred_keys},
        bin_vars=tuple(sorted(guard_bits, key=lambda v: str(v)))
        if guard_bits is not None
        else tuple(),
        table_rhs_display=table_rhs_display,
    )
    return pred_to_guard_code.format_table("Partition update predicate -> guards map")


def build_partitioned_update_chain(
    updates_by_var: dict[str, set[Update]],
    inputs,
    *,
    state_prefix: str = "c_",
    selector_prefix: str = "con_act_",
    use_curr_input_snapshots: bool = False,
    group_input_dependent_first: bool | None = None,
    use_qe_equivalent_update_guard_fusion: bool = False,
    symbol_table=None,
) -> PartitionedUpdateChain:
    apply_curr_input_snapshots = use_curr_input_snapshots
    if group_input_dependent_first is None:
        group_input_dependent_first = not apply_curr_input_snapshots
    (
        partitions,
        effective_updates_by_var,
        rewritten_to_original_update,
        snapshot_state_vars,
        snapshot_inputs,
        input_snapshot_subst,
    ) = partition_updates(
        updates_by_var,
        inputs,
        group_input_dependent_first=group_input_dependent_first,
        apply_curr_input_snapshots=apply_curr_input_snapshots,
    )

    partition_keys = ["_".join(sorted(part)) for part in partitions]

    states: set[str] = set()
    transitions: list[Transition] = []
    all_con_act_vars: set[Variable] = set()
    update_key_to_guard_terms: dict[tuple[str, str], list[Formula]] = {}
    update_key_to_guard_display_terms: dict[tuple[str, str], list[str]] = {}
    update_key_to_rhs: dict[tuple[str, str], Formula] = {}
    update_keys_by_var: dict[str, set[tuple[str, str]]] = {}
    update_key_to_pred_keys: dict[tuple[str, str], set[str]] = {}
    update_key_in_first_partition: dict[tuple[str, str], bool] = {}
    canonical_pred_keys_cache: dict[Update, list[str]] = {}

    eval_state = "eval"
    if len(partition_keys) == 0:
        states.add(eval_state)
        transitions.append(Transition(eval_state, true(), [], [], eval_state))
        return PartitionedUpdateChain(
            states=states,
            initial_state=eval_state,
            eval_state=eval_state,
            transitions=transitions,
            controller_events=all_con_act_vars,
            update_predicate_key_to_guard={},
            snapshot_state_vars=snapshot_state_vars,
        )

    partition_items = []
    for i in range(len(partitions)):
        part_key = partition_keys[i]
        vars_in_part = sorted(partitions[i])
        if apply_curr_input_snapshots and i == 0:
            # First partition still uses direct inputs; snapshots are taken when
            # leaving this state so later partitions can depend on curr_*.
            updates_for_part = [updates_by_var[v] for v in vars_in_part]
        else:
            updates_for_part = [effective_updates_by_var[v] for v in vars_in_part]
        combo_sources = [list(ups) for ups in updates_for_part if len(ups) > 0]
        combo_count = 1
        for ups in combo_sources:
            combo_count *= len(ups)
        partition_items.append((part_key, combo_sources, combo_count))

    eval_state = state_prefix + partition_items[0][0]
    initial_state = eval_state
    snapshot_actions = (
        [Update(input_snapshot_subst[inp], inp) for inp in snapshot_inputs]
        if apply_curr_input_snapshots and len(snapshot_state_vars) > 0
        else []
    )
    input_to_curr = input_snapshot_subst if apply_curr_input_snapshots else {}

    for j, (part_key, combo_sources, combo_count) in enumerate(partition_items):
        state = state_prefix + part_key
        state_var = Variable(state)
        states.add(state)
        last_partition = j == len(partition_items) - 1
        next_state = (
            eval_state if last_partition else state_prefix + partition_items[j + 1][0]
        )

        selector_vars, selector_map = binary_rep(
            [Variable(str(k)) for k in range(combo_count)],
            selector_prefix,
        )
        all_con_act_vars.update(selector_vars)
        selector_values = list(selector_map.values())
        extra_snapshot_actions = (
            snapshot_actions if apply_curr_input_snapshots and j == 0 else []
        )

        combo_iter = product(*combo_sources) if len(combo_sources) > 0 else [()]
        for i, act_tuple in enumerate(combo_iter):
            act_guard = selector_values[i]
            pred_guard = (
                act_guard
                if state == eval_state
                else BiOp(neg(state_var), "U", conjunct(state_var, act_guard))
            )
            transitions.append(
                Transition(
                    state,
                    act_guard,
                    list(act_tuple) + extra_snapshot_actions,
                    [],
                    next_state,
                )
            )

            for upd in act_tuple:
                original_upd = rewritten_to_original_update.get(upd, upd)
                rhs = strip_mathexpr(original_upd.right)
                upd_key = (str(original_upd.left), str(rhs))
                selector_key = Variable(str(i))
                selector_code = selector_map._table_rhs_display.get(
                    selector_key, str(act_guard)
                )
                pred_guard_display = (
                    selector_code
                    if state == eval_state
                    else f"(!{state} U ({state} && {selector_code}))"
                )
                update_key_to_rhs[upd_key] = rhs
                update_keys_by_var.setdefault(str(original_upd.left), set()).add(
                    upd_key
                )
                update_key_in_first_partition[upd_key] = bool(j == 0)
                update_key_to_guard_terms.setdefault(upd_key, []).append(pred_guard)
                update_key_to_guard_display_terms.setdefault(upd_key, []).append(
                    pred_guard_display
                )
                pred_keys = canonical_pred_keys_cache.get(original_upd)
                if pred_keys is None:
                    pred_keys = _canonical_update_predicate_keys(original_upd)
                    canonical_pred_keys_cache[original_upd] = pred_keys
                for pred_key in pred_keys:
                    update_key_to_pred_keys.setdefault(upd_key, set()).add(pred_key)

    def _join_unique_disjuncts(terms: list[str]) -> str:
        unique_terms = list(dict.fromkeys(terms))
        if len(unique_terms) == 0:
            return "FALSE"
        if len(unique_terms) == 1:
            return unique_terms[0]
        return " || ".join(unique_terms)

    update_key_to_guard = {
        k: disjunct_formula_set(vs) for k, vs in update_key_to_guard_terms.items()
    }
    update_key_to_guard_display = {
        k: _join_unique_disjuncts(vs)
        for k, vs in update_key_to_guard_display_terms.items()
    }

    if use_qe_equivalent_update_guard_fusion and len(update_keys_by_var) > 0:
        qe_symbol_table = dict(symbol_table)
        for inp in snapshot_inputs:
            inp_name = str(inp)
            curr_name = "curr_" + inp_name
            if curr_name not in qe_symbol_table and inp_name in qe_symbol_table:
                qe_symbol_table[curr_name] = qe_symbol_table[inp_name]
        rhs_for_qe = {}
        for upd_key, rhs in update_key_to_rhs.items():
            if (
                apply_curr_input_snapshots
                and not update_key_in_first_partition.get(upd_key, False)
            ):
                rhs_for_qe[upd_key] = rhs.replace_formulas(input_to_curr)
            else:
                rhs_for_qe[upd_key] = rhs

        def _qe_equivalence_cond(
            update_var: str, left_rhs: Formula, right_rhs: Formula
        ) -> Formula:
            var_type = qe_symbol_table[update_var]
            smt_ty = BOOL if var_type == BOOLEAN else INT
            eq_formula = BiOp(strip_mathexpr(left_rhs), "=", strip_mathexpr(right_rhs))
            neq_smt = neg(eq_formula).to_smt(qe_symbol_table)[0]
            quantified = Not(Exists([Symbol(update_var, smt_ty)], neq_smt))
            qe = quantifier_elimination(quantified)
            return simplify_formula_with_math(fnode_to_formula(qe), qe_symbol_table)

        merged_update_key_to_guard = {}
        merged_update_key_to_guard_display = {}
        for var_name, upd_keys in update_keys_by_var.items():
            upd_keys_sorted = sorted(upd_keys)
            for target_key in upd_keys_sorted:
                guard_terms = [update_key_to_guard[target_key]]
                display_terms = [update_key_to_guard_display[target_key]]
                target_rhs = rhs_for_qe[target_key]
                for other_key in upd_keys_sorted:
                    if other_key == target_key:
                        continue
                    other_rhs = rhs_for_qe[other_key]
                    if isinstance(target_rhs, NonDeterministic) or isinstance(
                        other_rhs, NonDeterministic
                    ):
                        # Nondeterministic updates intentionally represent a
                        # strict "other" branch; do not merge guards via QE.
                        continue
                    eq_cond = _qe_equivalence_cond(var_name, target_rhs, other_rhs)
                    if is_tautology(eq_cond, qe_symbol_table):
                        guard_terms.append(update_key_to_guard[other_key])
                        display_terms.append(update_key_to_guard_display[other_key])
                    elif sat(eq_cond, qe_symbol_table):
                        guard_terms.append(
                            conjunct(eq_cond, update_key_to_guard[other_key])
                        )
                        display_terms.append(
                            f"({eq_cond} && {update_key_to_guard_display[other_key]})"
                        )
                merged_update_key_to_guard[target_key] = disjunct_formula_set(
                    guard_terms
                )
                merged_update_key_to_guard_display[target_key] = _join_unique_disjuncts(
                    display_terms
                )
        update_key_to_guard = merged_update_key_to_guard
        update_key_to_guard_display = merged_update_key_to_guard_display

    update_predicate_key_to_guard_terms = {}
    update_predicate_key_to_guard_display_terms = {}
    for upd_key, guard in update_key_to_guard.items():
        for pred_key in update_key_to_pred_keys.get(upd_key, set()):
            update_predicate_key_to_guard_terms.setdefault(pred_key, []).append(guard)
            update_predicate_key_to_guard_display_terms.setdefault(pred_key, []).append(
                update_key_to_guard_display[upd_key]
            )
    update_predicate_key_to_guard = {
        k: disjunct_formula_set(vs)
        for k, vs in update_predicate_key_to_guard_terms.items()
    }
    update_predicate_key_to_guard_display = {
        k: _join_unique_disjuncts(vs)
        for k, vs in update_predicate_key_to_guard_display_terms.items()
    }

    map_str = format_update_predicate_guard_map(
        update_predicate_key_to_guard,
        update_predicate_key_to_guard_display=update_predicate_key_to_guard_display,
        guard_bits=all_con_act_vars,
    )
    print(map_str)
    logging.info(map_str)

    return PartitionedUpdateChain(
        states=states,
        initial_state=initial_state,
        eval_state=eval_state,
        transitions=transitions,
        controller_events=all_con_act_vars,
        update_predicate_key_to_guard=update_predicate_key_to_guard,
        snapshot_state_vars=snapshot_state_vars,
    )


def partition_updates(
    updates: dict[str, set[Update]],
    inputs,
    *,
    group_input_dependent_first: bool = True,
    apply_curr_input_snapshots: bool = False,
) -> tuple[
    list[set[str]],
    dict[str, set[Update]],
    dict[Update, Update],
    set[Variable],
    list[Variable],
    dict[Variable, Variable],
]:
    """
    Partition variables into sets of variables that should be updated together.
    """
    update_vars = set(updates.keys())
    input_names = {str(v) for v in inputs}

    dep_names_by_var: dict[str, set[str]] = {}
    input_dependent = set()
    for var, ups in updates.items():
        deps: set[str] = set()
        is_input_dependent = False
        for u in ups:
            for dep_var in u.right.variablesin():
                dep_name = str(dep_var)
                deps.add(dep_name)
                if dep_name in input_names:
                    is_input_dependent = True
        dep_names_by_var[var] = deps
        if is_input_dependent:
            input_dependent.add(var)

    remaining = update_vars
    adjacency: dict[str, set[str]] = {v: set() for v in remaining}

    for var in remaining:
        for dep in dep_names_by_var.get(var, set()):
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
        for dep in dep_names_by_var.get(var, set()):
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

    if group_input_dependent_first and input_dependent and len(ordered) > 1:
        first = None
        for i, p in enumerate(ordered):
            if input_dependent.issubset(p):
                first = i
                break
        if first is not None:
            first_part = ordered[first]
            remaining_parts = ordered[:first] + ordered[first + 1 :]
        else:
            input_parts = {
                i: p for i, p in enumerate(ordered) if not p.isdisjoint(input_dependent)
            }
            first_part = set(
                itertools.chain.from_iterable(p for p in input_parts.values())
            )
            remaining_parts = [
                p for i, p in enumerate(ordered) if i not in input_parts.keys()
            ]

        ordered = [first_part] + remaining_parts

    effective_updates_by_var = updates
    rewritten_to_original_update: dict[Update, Update] = {}
    snapshot_state_vars: set[Variable] = set()
    snapshot_inputs: list[Variable] = []
    input_snapshot_subst: dict[Variable, Variable] = {}

    if apply_curr_input_snapshots and len(ordered) > 1:
        input_by_name = {str(inp): inp for inp in inputs}
        snapshot_input_names: set[str] = set()
        for part in ordered[1:]:
            for var_name in part:
                for dep_name in dep_names_by_var.get(var_name, set()):
                    if dep_name in input_by_name:
                        snapshot_input_names.add(dep_name)
        snapshot_inputs = [input_by_name[n] for n in sorted(snapshot_input_names)]

        if len(snapshot_inputs) > 0:
            input_snapshot_subst = {
                inp: Variable("curr_" + inp.name) for inp in snapshot_inputs
            }
            snapshot_state_vars = set(input_snapshot_subst.values())
            effective_updates_by_var = {}
            partition_var_to_index = {}
            for i, part in enumerate(ordered):
                for var_name in part:
                    partition_var_to_index[var_name] = i
            for var_name, ups in updates.items():
                rewrite_inputs_here = partition_var_to_index.get(var_name, 0) > 0
                rewritten = set()
                for u in ups:
                    if rewrite_inputs_here:
                        new_u = Update(
                            u.left, u.right.replace_formulas(input_snapshot_subst)
                        )
                    else:
                        new_u = u
                    rewritten.add(new_u)
                    rewritten_to_original_update[new_u] = u
                effective_updates_by_var[var_name] = rewritten

    return (
        ordered,
        effective_updates_by_var,
        rewritten_to_original_update,
        snapshot_state_vars,
        snapshot_inputs,
        input_snapshot_subst,
    )


def update_combinations(
    updates: Iterator[Iterator[Update]],
) -> list[tuple[Update, ...]]:
    if not updates:
        return []
    return list(product(*[list(ups) for ups in updates if len(ups) > 0]))
