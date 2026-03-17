import config
from typing import List, Optional

from pysmt.logics import BOOL
from pysmt.shortcuts import Exists, And, Symbol
from pysmt.typing import INT

from analysis.smt_checker import quantifier_elimination
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


def determinise(raw_transitions: dict[str, list[Transition]], game_index, symbol_table):
    """Determinise outgoing transitions by adding fresh propositions controlled by controller.

    Guards produced per source must be mutually exclusive and complete to avoid
    introducing implicit stutter transitions in later completion steps.
    """
    con_vars = set()
    debug = config.Config.getConfig().debug
    new_transitions = []
    lose_transitions = []
    for src, trans in raw_transitions.items():
        src_no_guard_enabled = neg(disjunct_formula_set(t.condition for t in trans))

        (
            equiv_map,
            sat_map,
            equiv_parts,
            _,
        ) = condition_choices(trans, symbol_table)
        new_src_trans = []
        equiv_index = 0
        sat_index = 0

        eq_trigger_to_add = {t: [] for t in trans}
        sat_trigger_to_add = {t: [] for t in trans}

        def _assert_distinguishable(trigger_list, base_transition: Transition):
            if debug and not sat(
                conjunct_formula_set(trigger_list),
                symbol_table | {str(v): BOOLEAN for v in con_vars},
            ):
                raise Exception(
                    "In processing transitions from state "
                    + str(src)
                    + ", could not distinguish transition: \n"
                    + str(base_transition)
                )

        for t, equiv_part_minus_t in equiv_map.items():
            raw_equiv_triggers = [
                Variable("equiv_" + str(no))
                for no in range(0, len(equiv_part_minus_t) + 1)
            ]
            eq_con_events, equiv_binary_map = binary_rep(
                raw_equiv_triggers,
                "eq_con_" + str(game_index) + "_" + str(equiv_index) + "_",
                printing=False,
            )
            equiv_index += 1
            con_vars.update(eq_con_events)
            eq_trigger_to_add[t].append(equiv_binary_map[raw_equiv_triggers[0]])
            for i, tt in enumerate(equiv_part_minus_t):
                eq_trigger_to_add[tt].append(
                    equiv_binary_map[raw_equiv_triggers[i + 1]]
                )

        # order is important here
        # for t = trans[n], sat_map[t] only contains sat tt in trans[n + 1:]
        for t in trans:
            if t in sat_map.keys():
                if len(sat_map[t]) == 0 or t in equiv_parts.keys():
                    continue

                ts_to_distinguish = set()
                for _t in sat_map[t]:
                    if _t in equiv_parts.keys():
                        ts_to_distinguish.add(equiv_parts[_t])
                    else:
                        ts_to_distinguish.add(_t)
                ts_to_distinguish = list(ts_to_distinguish)

                if debug:
                    if t in equiv_map.keys():
                        for tt in equiv_map[t]:
                            if tt in sat_map.keys():
                                raise Exception(
                                    "Later equiv transition also in sat map"
                                )

                raw_sat_triggers = [
                    Variable("sat_" + str(no))
                    for no in range(0, len(ts_to_distinguish) + 1)
                ]
                sat_con_events, sat_binary_map = binary_rep(
                    raw_sat_triggers,
                    "sat_con_" + str(game_index) + "_" + str(sat_index) + "_",
                    printing=False,
                )
                sat_index += 1
                con_vars.update(sat_con_events)

                one_of_the_rest = disjunct_formula_set(
                    {tt.condition for tt in ts_to_distinguish}
                )

                # need to add below trans also to equiv transitions
                equiv_to_t = [t]
                if t in equiv_map.keys():
                    equiv_to_t.extend(equiv_map[t])
                elif t in equiv_parts.keys():
                    equiv_to_t.extend(equiv_map[equiv_parts[t]])

                if len(equiv_to_t) > 1:
                    if not is_tautology(one_of_the_rest, symbol_table):
                        if not sat(
                            conjunct(t.condition, neg(one_of_the_rest)),
                            symbol_table,
                        ):
                            for eq_t in equiv_to_t:
                                sat_trigger_to_add[eq_t].append(
                                    sat_binary_map[raw_sat_triggers[0]]
                                )
                                _assert_distinguishable(sat_trigger_to_add[eq_t], t)
                        else:
                            trigger_cond = implies(
                                one_of_the_rest,
                                sat_binary_map[raw_sat_triggers[0]],
                            )
                            for eq_t in equiv_to_t:
                                sat_trigger_to_add[eq_t].append(trigger_cond)
                    else:
                        for eq_t in equiv_to_t:
                            sat_trigger_to_add[eq_t].append(
                                sat_binary_map[raw_sat_triggers[0]]
                            )
                            _assert_distinguishable(sat_trigger_to_add[eq_t], t)

                if len(ts_to_distinguish) > 0:
                    if len(equiv_to_t) == 1:
                        sat_trigger_to_add[t].append(
                            sat_binary_map[raw_sat_triggers[0]]
                        )
                    for i, tt in enumerate(ts_to_distinguish):
                        equiv_to_tt = [tt]
                        if tt in equiv_map.keys():
                            equiv_to_tt.extend(equiv_map[tt])
                        elif tt in equiv_parts.keys():
                            equiv_to_tt.extend(equiv_map[equiv_parts[tt]])

                        one_of_the_rest = disjunct_formula_set(
                            {ttt.condition for ttt in ts_to_distinguish if ttt != tt}
                            | {t.condition}
                        )
                        if not is_tautology(one_of_the_rest, symbol_table):
                            if not sat(
                                conjunct(tt.condition, neg(one_of_the_rest)),
                                symbol_table,
                            ):
                                for eq_tt in equiv_to_tt:
                                    sat_trigger_to_add[eq_tt].append(
                                        sat_binary_map[raw_sat_triggers[i + 1]]
                                    )
                                    _assert_distinguishable(
                                        sat_trigger_to_add[eq_tt], t
                                    )
                            else:
                                trigger_cond = implies(
                                    one_of_the_rest,
                                    sat_binary_map[raw_sat_triggers[i + 1]],
                                )
                                for eq_tt in equiv_to_tt:
                                    sat_trigger_to_add[eq_tt].append(trigger_cond)
                                    _assert_distinguishable(
                                        sat_trigger_to_add[eq_tt], t
                                    )
                        else:
                            for eq_tt in equiv_to_tt:
                                sat_trigger_to_add[eq_tt].append(
                                    sat_binary_map[raw_sat_triggers[i + 1]]
                                )
                                _assert_distinguishable(sat_trigger_to_add[eq_tt], t)

        for t in trans:
            trigger_terms = eq_trigger_to_add[t] + sat_trigger_to_add[t]
            trigger_condition = conjunct_formula_set(trigger_terms)
            guarded_conditions = [
                simplify_formula_with_math(
                    conjunct(
                        t.condition,
                        trigger_condition,
                    ),
                    symbol_table | {str(v): BOOLEAN for v in con_vars},
                )
            ]

            for guarded_cond in guarded_conditions:
                if not sat(
                    guarded_cond, symbol_table | {str(v): BOOLEAN for v in con_vars}
                ):
                    continue
                new_t = Transition(
                    t.src,
                    guarded_cond,
                    t.action,
                    [],
                    t.tgt,
                )
                new_t.set_predicate_upgrades(t.pred_upgrades)
                new_src_trans.append(new_t)

        new_transitions.extend(new_src_trans)
        if sat(
            src_no_guard_enabled,
            symbol_table | {str(v): BOOLEAN for v in con_vars},
        ):
            lose_transitions.append(
                Transition(src, src_no_guard_enabled, [], [], "lose")
            )

        if debug:
            for t in new_transitions + lose_transitions:
                for tt in new_transitions + lose_transitions:
                    if t == tt or t.src != tt.src:
                        continue
                    if sat(
                        conjunct(t.condition, tt.condition),
                        symbol_table | {str(v): BOOLEAN for v in con_vars},
                    ):
                        raise Exception(
                            "After processing, transitions from state "
                            + str(src)
                            + " still have non-distinguishable conditions: \n"
                            + str(t)
                            + "\n"
                            + str(tt)
                        )

    return new_transitions, lose_transitions, con_vars


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
