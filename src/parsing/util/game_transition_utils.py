import re

import config
from typing import List, Optional

from pysmt.logics import BOOL
from pysmt.shortcuts import Exists, And, Symbol
from pysmt.typing import INT

from analysis.smt_checker import quantifier_elimination
from analysis.sat_context import IncrementalSatContext, NonIncrementalSatContext
from programs.program import Program
from programs.transition import Transition
from programs.util import binary_rep
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.types.types import BOOLEAN
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.util import (
    atomic_predicates,
    fnode_to_formula,
    is_conjunction_of_atoms,
    is_tautology,
    strip_mathexpr,
    true,
    neg,
    conjunct,
    disjunct_formula_set,
    conjunct_formula_set,
    implies,
    sat,
    false,
    simplify_formula_with_math,
    iff,
    cancel_double_negations,
    disjunct,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from parsing.util.issy.reductions.ltl.formula_utils import (
    reduce_formula_set_up_to_equivalence,
)


def _merge_partition_regions(
    regions: list[tuple[Formula, frozenset[int]]],
    symbol_table,
    sat_ctx=None,
) -> list[tuple[Formula, frozenset[int]]]:
    grouped: dict[frozenset[int], list[Formula]] = {}
    for cond, enabled in regions:
        if len(enabled) == 0:
            continue
        if not sat(cond, symbol_table, sat_ctx=sat_ctx):
            continue
        grouped.setdefault(enabled, []).append(cond)

    merged = []
    for enabled, conds in grouped.items():
        merged_cond = simplify_formula_with_math(
            disjunct_formula_set(conds), symbol_table
        )
        if sat(merged_cond, symbol_table, sat_ctx=sat_ctx):
            merged.append((merged_cond, enabled))
    return merged


def _add_guard_to_partition(
    regions: list[tuple[Formula, frozenset[int]]],
    guard: Formula,
    transition_index: int,
    symbol_table,
    overlap_adjacency: Optional[list[set[int]]] = None,
    sat_ctx=None,
) -> list[tuple[Formula, frozenset[int]]]:
    if not sat(guard, symbol_table, sat_ctx=sat_ctx):
        return regions

    if len(regions) == 0:
        return [
            (
                guard,
                frozenset({transition_index}),
            )
        ]

    out: list[tuple[Formula, frozenset[int]]] = []
    remaining = guard

    for region_cond, enabled in regions:
        if overlap_adjacency is not None:
            neighbors = overlap_adjacency[transition_index]
            # region_cond implies every guard in `enabled`. If any enabled guard
            # is disjoint from incoming guard, overlap is impossible.
            if any(e != transition_index and e not in neighbors for e in enabled):
                out.append((region_cond, enabled))
                continue

        overlap = conjunct(region_cond, guard)
        region_only = conjunct(region_cond, neg(guard))
        if sat(overlap, symbol_table, sat_ctx=sat_ctx):
            out.append((overlap, frozenset(set(enabled) | {transition_index})))
        if sat(region_only, symbol_table, sat_ctx=sat_ctx):
            out.append((region_only, enabled))
        remaining = conjunct(remaining, neg(region_cond))

    if sat(remaining, symbol_table, sat_ctx=sat_ctx):
        out.append((remaining, frozenset({transition_index})))

    return _merge_partition_regions(out, symbol_table, sat_ctx=sat_ctx)


def _transition_overlap_components(
    trans: list[Transition],
    symbol_table,
    sat_ctx=None,
) -> tuple[list[list[int]], list[set[int]]]:
    """Partition transitions into overlap-connected components.

    Transitions in different components are pairwise disjoint, so they do not need
    joint selector encoding/partitioning.
    """
    if len(trans) == 0:
        return [], []
    if len(trans) == 1:
        return [[0]], [set()]

    adjacency: dict[int, set[int]] = {i: set() for i in range(len(trans))}

    def _connect(i: int, j: int):
        adjacency[i].add(j)
        adjacency[j].add(i)

    # Build overlap graph directly: edge(i, j) iff guards overlap.
    for i in range(len(trans)):
        cond_i = trans[i].condition
        for j in range(i + 1, len(trans)):
            cond_j = trans[j].condition
            if sat(conjunct(cond_i, cond_j), symbol_table, sat_ctx=sat_ctx):
                _connect(i, j)

    seen = set()
    components = []
    for i in range(len(trans)):
        if i in seen:
            continue
        stack = [i]
        seen.add(i)
        component = []
        while stack:
            cur = stack.pop()
            component.append(cur)
            for nxt in adjacency[cur]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        components.append(sorted(component))
    adjacency_list = [adjacency[i] for i in range(len(trans))]
    return components, adjacency_list


def determinise(raw_transitions: dict[str, list[Transition]], game_index, symbol_table):
    """Determinise transitions by explicit disjoint region partitioning.

    For each source state:
    - build disjoint guard regions labelled with the set of enabled raw transitions
    - add selector bits only on regions with multiple enabled transitions
    - emit one guarded transition per original transition index

    This guarantees:
    - pairwise disjoint emitted guards
    - coverage of raw guard region for all selector valuations
    """
    con_vars = set()
    debug = config.Config.getConfig().debug
    new_transitions = []

    for src, trans in raw_transitions.items():
        if len(trans) == 0:
            continue

        sat_ctx_cls = (
            IncrementalSatContext
            if config.Config.getConfig().opt_incremental_smt
            else NonIncrementalSatContext
        )
        with sat_ctx_cls(symbol_table) as sat_ctx:
            guard_terms_by_transition: dict[int, list[Formula]] = {
                idx: [] for idx in range(len(trans))
            }

            components, overlap_adjacency = _transition_overlap_components(
                trans, symbol_table, sat_ctx=sat_ctx
            )
            selector_region_index = 0
            for component in components:
                if len(component) == 1:
                    idx = component[0]
                    guard_terms_by_transition[idx].append(trans[idx].condition)
                    continue

                regions: list[tuple[Formula, frozenset[int]]] = []
                for idx in component:
                    regions = _add_guard_to_partition(
                        regions,
                        trans[idx].condition,
                        idx,
                        symbol_table,
                        overlap_adjacency=overlap_adjacency,
                        sat_ctx=sat_ctx,
                    )

                for region_cond, enabled in regions:
                    ordered_enabled = sorted(enabled)
                    if len(ordered_enabled) == 1:
                        guard_terms_by_transition[ordered_enabled[0]].append(
                            region_cond
                        )
                        continue

                    raw_selector_choices = [
                        Variable(f"sat_choice_{i}") for i in range(len(ordered_enabled))
                    ]
                    sat_con_events, sat_binary_map = binary_rep(
                        raw_selector_choices,
                        "sat_con_" + str(game_index) + "_",
                        printing=False,
                    )
                    selector_region_index += 1
                    con_vars.update(sat_con_events)

                    for local_choice_idx, transition_idx in enumerate(ordered_enabled):
                        selector_guard = sat_binary_map[
                            raw_selector_choices[local_choice_idx]
                        ]
                        guarded_piece = conjunct(region_cond, selector_guard)
                        guard_terms_by_transition[transition_idx].append(guarded_piece)

        sem_symbol_table = symbol_table | {str(v): BOOLEAN for v in con_vars}
        new_src_transitions: list[Transition] = []
        sem_sat_ctx_cls = (
            IncrementalSatContext
            if config.Config.getConfig().opt_incremental_smt
            else NonIncrementalSatContext
        )
        with sem_sat_ctx_cls(sem_symbol_table) as sem_sat_ctx:
            for idx, t in enumerate(trans):
                terms = guard_terms_by_transition[idx]
                if len(terms) == 0:
                    continue
                guarded_cond = simplify_formula_with_math(
                    disjunct_formula_set(terms),
                    sem_symbol_table,
                )
                if not sat(guarded_cond, sem_symbol_table, sat_ctx=sem_sat_ctx):
                    continue
                new_t = Transition(
                    t.src,
                    guarded_cond,
                    t.action,
                    [],
                    t.tgt,
                )
                new_t.set_predicate_upgrades(t.pred_upgrades)
                new_src_transitions.append(new_t)
        new_transitions.extend(new_src_transitions)

        if debug:
            for i, t in enumerate(new_src_transitions):
                for tt in new_src_transitions[i + 1 :]:
                    if sat(conjunct(t.condition, tt.condition), sem_symbol_table):
                        raise Exception(
                            "determinise produced overlapping source guards for "
                            + str(src)
                            + ":\n"
                            + str(t)
                            + "\n"
                            + str(tt)
                        )
            raw_coverage = disjunct_formula_set(t.condition for t in trans)
            det_coverage = disjunct_formula_set(
                t.condition for t in new_src_transitions
            )
            uncovered_raw = conjunct(raw_coverage, neg(det_coverage))
            if sat(uncovered_raw, sem_symbol_table):
                raise Exception(
                    "determinise produced incomplete source coverage for " + str(src)
                )

    return new_transitions, con_vars


def condition_choices(transitions: List[Transition], symbol_table) -> tuple[
    dict[Transition, list[Transition]],
    dict[Transition, list[Transition]],
    dict[Transition, Transition],
    Optional[Formula],
]:
    # returns two mappings and an optional condition:
    # 1) transitions grouped with others that have equivalent conditions
    # 2) transitions mapped to others with satisfiable (but non-equivalent) conditions
    # 3) an optional condition returned when the transitions are not complete w.r.t. pre-state,
    # the condition describes when no transition is triggerable

    equiv_map: dict[Transition, list[Transition]] = {}
    compat_map: dict[Transition, list[Transition]] = {}

    equiv_parts: dict[Transition, Transition] = {}
    n = len(transitions)
    found_equiv = set()
    for i in range(n):
        t_i = transitions[i]
        cond_i = t_i.condition
        # if we already found equivalent transitions for t_i, skip
        # it's satisfiability and equivalence with others has already been handled
        if t_i in found_equiv:
            continue
        for j in range(i + 1, n):
            t_j = transitions[j]
            if t_j in found_equiv:
                continue

            cond_j = t_j.condition
            if sat(conjunct(cond_i, cond_j), symbol_table):
                if sat(conjunct(cond_i, neg(cond_j)), symbol_table) or sat(
                    conjunct(cond_j, neg(cond_i)), symbol_table
                ):
                    compat_map.setdefault(t_i, list()).append(t_j)
                else:
                    equiv_map.setdefault(t_i, list()).append(t_j)
                    found_equiv.add(t_j)
                    equiv_parts[t_j] = t_i
    no_trans_triggered = neg(disjunct_formula_set(t.condition for t in transitions))
    if not sat(no_trans_triggered, symbol_table):
        no_trans_triggered = None
    return equiv_map, compat_map, equiv_parts, no_trans_triggered


def independent_games(vars, games):
    if len(games) == 1:
        return [games]

    vars_to_games = {}
    for i, s in enumerate(vars):
        vars_to_games[str(s)] = []

    # detect dependence based on vars used in transitions
    def get_vars_in_game(i):
        game = games[i]
        vars_in_game = set()
        _, _, _, transitions = game
        for _, formula, _ in transitions:
            for v in formula.variablesin():
                if v.is_next():
                    vars_in_game.add(str(v.prev_rep()))
                else:
                    vars_in_game.add(str(v))
        return vars_in_game

    for i in range(len(games)):
        vars_in_game = get_vars_in_game(i)
        for v in vars_in_game:
            if v in vars_to_games.keys():
                vars_to_games[v].append(i)

    # transitively collect games based on shared variables
    visited_games = set()
    independent_game_sets = []

    for i in range(len(games)):
        if i in visited_games:
            continue
        to_visit = [i]
        current_set = set()

        while to_visit:
            current_game = to_visit.pop()
            if current_game in visited_games:
                continue
            visited_games.add(current_game)
            current_set.add(current_game)

            vars_in_current_game = get_vars_in_game(current_game)
            for v in vars_in_current_game:
                for dependent_game in vars_to_games.get(v, []):
                    if dependent_game not in visited_games:
                        to_visit.append(dependent_game)

        independent_game_sets.append(list(current_set))
    return [[games[g] for g in s] for s in independent_game_sets]


def normalise_update(f):
    updates = []
    to_replace = {}
    if isinstance(u := f, Variable):
        updates.append(BiOp(u, "=", true()))
        updates.append(BiOp(u, "=", false()))
        to_replace[u] = BiOp(u, "=", true())
        to_replace[neg(u)] = BiOp(u, "=", false())
    elif isinstance(u, UniOp):
        return normalise_update(u)
    elif isinstance(u, BiOp):
        if (
            isinstance(u.left, Variable)
            and isinstance(u.right, Value)
            and isinstance(u.right, BoolAtoms)
        ):
            return normalise_update(u.left)
        elif (
            isinstance(u.right, Variable)
            and isinstance(u.left, Value)
            and isinstance(u.left, BoolAtoms)
        ):
            return normalise_update(u.right)
        elif u.op == "!=":
            updates, to_replace = normalise_update(BiOp(u.left, "=", u.right))
            to_replace[MathExpr(u)] = neg(BiOp(u.left, "=", u.right))
            to_replace[u] = neg(BiOp(u.left, "=", u.right))
        else:
            updates.append(u)
    return updates, to_replace


def _formula_to_transitions_raw(formula, symbol_table, guard_prefix=None):
    """Recursive normalization until residual atomic predicates are all next-sensitive.

    Strategy:
    - keep decomposing `|`, `&`, and next-sensitive `->`
    - hoist non-next conjuncts into guards
    - until we reach conjunction of predicates that all have primed variables
    - prune early with SAT checks
    """
    if guard_prefix is None:
        guard_prefix = true()

    def _all_atomic_predicates_have_primed_vars(f: Formula) -> bool:
        preds = atomic_predicates(f)
        if len(preds) == 0:
            return False
        for p in preds:
            if not any(
                isinstance(v, Variable) and v.is_next() for v in p.variablesin()
            ):
                return False
        return True

    def _visit(
        node: Formula, inherited_guard: Formula
    ) -> list[tuple[Formula, frozenset[Formula]]]:
        q = strip_mathexpr(node)

        if not _contains_next_var(q):
            f = conjunct(inherited_guard, q)
            return [(f, frozenset())] if sat(f, symbol_table) else []

        if _all_atomic_predicates_have_primed_vars(q):
            if is_conjunction_of_atoms(q):
                return [
                    (
                        inherited_guard,
                        frozenset(q.sub_formulas_up_to_associativity()),
                    )
                ]

        if isinstance(q, BiOp) and q.op == "|":
            out = []
            for child in q.sub_formulas_up_to_associativity():
                out.extend(_visit(child, inherited_guard))
            return out

        if isinstance(q, BiOp) and q.op == "&":
            conjuncts = q.sub_formulas_up_to_associativity()
            guarded = [c for c in conjuncts if not _contains_next_var(c)]
            next_sensitive = [c for c in conjuncts if _contains_next_var(c)]

            local_guard = inherited_guard
            if len(guarded) > 0:
                local_guard = conjunct(local_guard, conjunct_formula_set(guarded))

            if len(next_sensitive) == 0:
                return [(local_guard, frozenset())]

            if len(next_sensitive) == 1:
                return _visit(next_sensitive[0], local_guard)

            child_with_results: list[list[tuple[Formula, frozenset[Formula]]]] = []
            for child in next_sensitive:
                child_with_results.append(_visit(child, local_guard))

            accumulated = [(true(), frozenset())]
            for child_results in child_with_results:
                next_accumulated = []
                seen = set()
                for acc_cond, acc_updates in accumulated:
                    for child_cond, child_updates in child_results:
                        merged_cond = conjunct(acc_cond, child_cond)
                        merged_updates = acc_updates | child_updates
                        if not sat(
                            conjunct_formula_set(
                                {merged_cond} | merged_updates
                            ).prev_rep(),
                            symbol_table,
                        ):
                            continue
                        key = (merged_cond, merged_updates)
                        if key in seen:
                            continue
                        seen.add(key)
                        next_accumulated.append(key)

                if len(next_accumulated) == 0:
                    return []
                accumulated = next_accumulated

            return accumulated

        if isinstance(q, BiOp) and q.op in {"->", "<->"}:
            expanded = _expand_next_implications(q)
            if str(expanded) != str(q):
                return _visit(expanded, inherited_guard)

        raise Exception(
            f"Unexpected non-atomic residual formula during compositional traversal: {q}"
        )

    return _visit(formula, guard_prefix)


def formula_to_transitions(formula, inputs, symbol_table):
    raw_results = _formula_to_transitions_raw(formula, symbol_table)
    if config.Config.getConfig().debug:
        new_choices = set()
        for cond, updates in raw_results:
            new_choices.add(conjunct(cond, conjunct_formula_set(updates)))
        new_f = disjunct_formula_set(new_choices)
        if not is_tautology(iff(formula, new_f), symbol_table):
            raise Exception(
                "Overall compositional extraction is not equivalent.\n\n"
                + str(formula)
                + "\nvs\n"
                + str(new_f)
            )
    return process_cond_updates(raw_results, inputs, symbol_table)


def process_cond_updates(results, inputs, symbol_table):
    trans = {}
    cond_to_u = {}
    for r in results:
        cond, u = r
        new_cond, new_u = clean_updates(u, inputs, symbol_table)
        if config.Config.getConfig().debug:
            g = conjunct(new_cond, cond)
            guard_has_next_vars = any(
                isinstance(v, Variable) and v.is_next() for v in g.variablesin()
            )
            if guard_has_next_vars:
                raise Exception(
                    "Guard still has next variables after cleaning: " + str(g)
                )
        cond_to_u.setdefault(cond, set()).add((new_u, new_cond))

    for cond, us in cond_to_u.items():
        for u, new_cond in us:
            if isinstance(new_cond, Value) and new_cond.is_true():
                new_new_cond = cond
            else:
                new_new_cond = conjunct(cond, new_cond)
            trans.setdefault(u, set()).add(new_new_cond)

    results = []
    for u, conds in trans.items():
        if len(conds) > 1:
            reduced_conds = reduce_formula_set_up_to_equivalence(conds, symbol_table)
        else:
            reduced_conds = conds
        if config.Config.getConfig().debug:
            if not is_tautology(
                implies(
                    conjunct(disjunct_formula_set(conds), conjunct_formula_set(u)),
                    disjunct_formula_set(reduced_conds),
                ),
                symbol_table,
            ):
                raise Exception("Reduction produced non-equivalent formula.\n\n")

        if len(conds) - len(reduced_conds) > 0:
            removed = set(conds) - set(reduced_conds)
            print("removed redundant conditions: " + ", ".join(map(str, removed)))

        c, new_u = add_pred_upgrades_as_conds(u)
        new_cond = conjunct(c, disjunct_formula_set(reduced_conds))
        if config.Config.getConfig().debug:
            if not is_tautology(
                implies(
                    conjunct(disjunct_formula_set(conds), conjunct_formula_set(u)),
                    new_cond,
                ),
                symbol_table,
            ):
                raise Exception(
                    "Produced non-equivalent formula.\n\n"
                    + str(disjunct_formula_set(conds))
                    + "\n vs \n"
                    + str(new_cond)
                )
        results.append((new_cond, [new_u]))

    return results


def add_pred_upgrades_as_conds(us):
    eq_update_map = {}
    pred_upgrades = set()
    new_updates = set()
    for u in us:
        if isinstance(u, BiOp) and u.op == "=":
            left, right = u.left, u.right
            if (
                isinstance(left, Variable)
                and left.is_next()
                and not any(v for v in right.variablesin() if v.is_next())
            ):
                eq_update_map[left] = right
                new_updates.add(u)
            else:
                pred_upgrades.add(u)
        else:
            pred_upgrades.add(u)

    new_conds = []
    for p in pred_upgrades:
        next_removed = p.replace_formulas(eq_update_map)
        if not any(v for v in next_removed.variablesin() if v.is_next()):
            new_conds.append(next_removed)
        else:
            new_updates.add(next_removed)
    return conjunct_formula_set(new_conds), new_updates


def clean_updates(
    updates: set[Formula], inputs, symbol_table
) -> tuple[Formula, frozenset[Formula]]:
    # collect all the equality updates (x' = f)
    # if any variable has more than two equality updates
    # do quantifier elimination to identify condition that makes them equivalent
    # then we keep only of them: if there is one with input vars, keep the one with least input vars
    # else keep the one with the least vars on the RHS
    eq_updates: dict[Variable, set[Formula]] = {}
    updates = [cancel_double_negations(strip_mathexpr(u)) for u in updates]
    for u in updates:
        if isinstance(u, BiOp) and u.op == "=":
            left = u.left
            if isinstance(left, Variable) and left.is_next():
                if left not in eq_updates.keys():
                    eq_updates[left] = {u}
                else:
                    eq_updates[left].add(u)
                continue
    new_conds = []
    updates_to_remove = []
    for v, us in eq_updates.items():
        if len(us) > 1:
            # for quantifier elimination, we construct the formula
            # exists v . (u1 & u2 & ... & un)
            elim_var = [
                Symbol(str(v), BOOL if symbol_table[str(v)] == BOOLEAN else INT)
            ]
            combined = conjunct_formula_set(us)
            quant_formula = Exists(
                elim_var,
                And(*combined.to_smt(symbol_table)),
            )
            ret = quantifier_elimination(quant_formula)
            rett = fnode_to_formula(ret)
            new_conds.append(rett)

            reduced_us = [
                u
                for u in us
                if not any(v for v in u.right.variablesin() if v in inputs)
            ]

            if len(reduced_us) == 0:
                reduced_us = us

            to_keep = min(reduced_us, key=lambda u: len(u.right.variablesin()))
            updates_to_remove.extend([u for u in us if u != to_keep])

    final_updates = {u for u in updates if u not in updates_to_remove}
    return conjunct_formula_set(new_conds), frozenset(final_updates)


__all__ = [
    "determinise",
    "condition_choices",
    "independent_games",
    "formula_to_transitions",
]


def _contains_next_var(formula: Formula) -> bool:
    return any(
        v for v in formula.variablesin() if isinstance(v, Variable) and v.is_next()
    )


def _expand_next_implications(formula: BiOp) -> Formula:
    op = formula.op
    left = formula.left
    right = formula.right
    if op == "->":
        return disjunct(neg(left), right)
    if op == "<->":
        return disjunct(conjunct(left, right), conjunct(neg(left), neg(right)))

    return BiOp(left, formula.op, right)


def _resolve_nondeterminism(
    program: Program,
    symbol_table,
    to_exclude_from_minigame,
):
    if program.deterministic:
        return program, None, to_exclude_from_minigame

    raw_transitions = {}
    for t in program.orig_ts:
        raw_transitions.setdefault(t.src, []).append(t)

    # Determinisation/merge may touch pre-existing helper/event vars that are
    # present on transitions but not yet in the shared symbol table.
    det_symbol_table = dict(symbol_table)
    for ev, ty in list(program.env_events) + list(program.con_events):
        det_symbol_table.setdefault(str(ev), ty)

    # Backstop for helper vars that may have been introduced earlier.
    helper_name_pattern = re.compile(r"^(eq_con_|sat_con_).+")
    for ts in raw_transitions.values():
        for t in ts:
            for v in t.condition.variablesin():
                name = v.name
                if name not in det_symbol_table and helper_name_pattern.match(name):
                    det_symbol_table[name] = BOOLEAN
                if v.is_next():
                    prev_name = v.prev_rep().name
                    if prev_name not in det_symbol_table and helper_name_pattern.match(
                        prev_name
                    ):
                        det_symbol_table[prev_name] = BOOLEAN

    # Create lose transitions from raw source-guard coverage before any
    # determinisation selectors are introduced.
    lose_transitions = _complete_raw_transitions_with_lose(
        raw_transitions,
        det_symbol_table,
    )

    det_transitions, new_con_vars = determinise(
        raw_transitions,
        "cp",
        det_symbol_table,
    )

    merge_symbol_table = det_symbol_table | {str(v): BOOLEAN for v in new_con_vars}

    def _merge_equivalent_transitions(
        transitions: list[Transition],
    ) -> list[Transition]:
        grouped = {}
        for t in transitions:
            sig = (
                str(t.src),
                str(t.tgt),
                tuple(sorted(str(a) for a in t.action)),
                tuple(sorted(str(p) for p in t.pred_upgrades)),
                tuple(sorted(str(o) for o in t.output)),
            )
            if sig not in grouped:
                grouped[sig] = {"rep": t, "conds": [t.condition]}
            else:
                grouped[sig]["conds"].append(t.condition)

        merged = []
        for entry in grouped.values():
            rep = entry["rep"]
            merged_cond = simplify_formula_with_math(
                disjunct_formula_set(entry["conds"]),
                merge_symbol_table,
            )
            merged_t = Transition(
                rep.src,
                merged_cond,
                list(rep.action),
                list(rep.output),
                rep.tgt,
            )
            merged_t.set_predicate_upgrades(list(rep.pred_upgrades))
            merged.append(merged_t)
        return merged

    all_transitions = _merge_equivalent_transitions(det_transitions + lose_transitions)

    new_con_events = list(program.con_events)
    symbol_table.update(det_symbol_table)
    if len(new_con_vars) > 0:
        symbol_table.update({str(v): BOOLEAN for v in new_con_vars})
        for v in new_con_vars:
            if not any(ev == v and ty == BOOLEAN for ev, ty in new_con_events):
                new_con_events.append((v, BOOLEAN))

    lose_var = None
    if any(t.tgt == "lose" for t in all_transitions):
        lose_var = "lose"
        if lose_var not in to_exclude_from_minigame:
            to_exclude_from_minigame.append(lose_var)

    init_values = []
    for var in program.local_vars_str:
        var_type = program.symbol_table[var]
        if var in program.init_var_values:
            init_values.append((var, var_type, program.init_var_values[var]))
        else:
            init_values.append((var, var_type))

    determinised_program = Program(
        program.name,
        set(program.states),
        program.initial_state,
        init_values,
        all_transitions,
        list(program.env_events),
        new_con_events,
        preprocess=False,
        emit_state_binary_map=False,
        is_determ=True,
    )
    return determinised_program, lose_var, to_exclude_from_minigame


def _complete_raw_transitions_with_lose(raw_transitions, symbol_table):
    lose_transitions = []
    for src, trans in raw_transitions.items():
        no_trans_triggered = neg(disjunct_formula_set(t.condition for t in trans))
        if sat(no_trans_triggered, symbol_table):
            lose_transitions.append(Transition(src, no_trans_triggered, [], [], "lose"))
    return lose_transitions
