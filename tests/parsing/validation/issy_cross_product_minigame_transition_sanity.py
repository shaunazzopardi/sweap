import argparse
from dataclasses import dataclass
from pathlib import Path

from analysis.smt_checker import quantifier_elimination
from pysmt.shortcuts import And, BOOL, Exists, Symbol
from .issy_cross_product_minigame_equivalence import (
    _parse_issy_raw,
    _build_pre_post_cross_product_programs,
)
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    fnode_to_formula,
    implies,
    is_tautology,
    neg,
    sat,
)
from prop_lang.variable import Variable


@dataclass
class MinigameTransitionSanityReport:
    ok: bool
    capability_failures: list[str]
    exit_failures: list[str]
    transition_preservation_failures: list[str]
    unsupported: list[str]


def _is_minigame_state_name(state_name: str) -> bool:
    return "_minigame_" in state_name


def _minigame_end_state(start_state: str) -> str:
    return start_state.split("_minigame_")[0]


def _next(v: Variable) -> Variable:
    return Variable(v.name + "'")


def _transition_step_formula(t: Transition):
    deterministic_updates = []
    for act in t.action:
        if isinstance(act.right, NonDeterministic):
            continue
        deterministic_updates.append(BiOp(_next(act.left), "=", act.right))
    return conjunct_formula_set([t.condition] + deterministic_updates)


def _projected_transition_signature(t: Transition, keep_lhs: set[str]) -> tuple:
    action_sig = tuple(
        sorted(
            (
                str(act.left),
                str(act.right),
                isinstance(act.right, NonDeterministic),
            )
            for act in t.action
            if str(act.left) in keep_lhs
        )
    )
    pred_sig = tuple(sorted(str(p) for p in t.pred_upgrades))
    output_sig = tuple(sorted(str(o) for o in t.output))
    return (str(t.src), str(t.tgt), str(t.condition), action_sig, pred_sig, output_sig)


def _projected_transition_signature_with_states(
    t: Transition,
    keep_lhs: set[str],
    src_state: str,
    tgt_state: str,
) -> tuple:
    action_sig = tuple(
        sorted(
            (
                str(act.left),
                str(act.right),
                isinstance(act.right, NonDeterministic),
            )
            for act in t.action
            if str(act.left) in keep_lhs
        )
    )
    pred_sig = tuple(sorted(str(p) for p in t.pred_upgrades))
    output_sig = tuple(sorted(str(o) for o in t.output))
    return (src_state, tgt_state, str(t.condition), action_sig, pred_sig, output_sig)


def _lose_relaxed_signature_with_states(
    t: Transition,
    src_state: str,
    tgt_state: str,
) -> tuple:
    pred_sig = tuple(sorted(str(p) for p in t.pred_upgrades))
    output_sig = tuple(sorted(str(o) for o in t.output))
    return (src_state, tgt_state, str(t.condition), pred_sig, output_sig)


def _lose_transition_semantically_preserved(
    pre_t: Transition,
    post_t: Transition,
    src_state: str,
    tgt_state: str,
    symbol_table: dict[str, str],
) -> bool:
    if str(post_t.src) != src_state or str(post_t.tgt) != tgt_state:
        return False
    if tuple(sorted(str(p) for p in pre_t.pred_upgrades)) != tuple(
        sorted(str(p) for p in post_t.pred_upgrades)
    ):
        return False
    if tuple(sorted(str(o) for o in pre_t.output)) != tuple(
        sorted(str(o) for o in post_t.output)
    ):
        return False
    return is_tautology(implies(pre_t.condition, post_t.condition), symbol_table) and is_tautology(
        implies(post_t.condition, pre_t.condition), symbol_table
    )


def _lose_target_preserved_ignoring_actions(
    pre_t: Transition,
    post_program,
    src_state: str,
    symbol_table: dict[str, str],
) -> bool:
    pre_pred = tuple(sorted(str(p) for p in pre_t.pred_upgrades))
    pre_out = tuple(sorted(str(o) for o in pre_t.output))
    for post_t in post_program.transitions:
        if str(post_t.src) != src_state or str(post_t.tgt) != "lose":
            continue
        if tuple(sorted(str(p) for p in post_t.pred_upgrades)) != pre_pred:
            continue
        if tuple(sorted(str(o) for o in post_t.output)) != pre_out:
            continue
        if _conditions_equivalent(pre_t.condition, post_t.condition, symbol_table):
            return True
    return False


def _qe_exists_controller_bool_vars(
    formula,
    symbol_table: dict[str, str],
    con_events: list[tuple[Variable, str]],
):
    con_bool_names = {
        str(v) for v, t in con_events if t == BOOLEAN and str(v) in symbol_table
    }
    con_bool_names.update(
        {
            name
            for name, t in symbol_table.items()
            if t == BOOLEAN
            and (
                name.startswith("eq_con_")
                or name.startswith("sat_con_")
                or name.startswith("game_con_")
            )
        }
    )
    relevant = [name for name in con_bool_names if Variable(name) in formula.variablesin()]
    if len(relevant) == 0:
        return formula
    qvars = [Symbol(name, BOOL) for name in sorted(relevant)]
    smt_formula = And(*formula.to_smt(symbol_table))
    projected = quantifier_elimination(Exists(qvars, smt_formula))
    return fnode_to_formula(projected)


def _pick_pre_transition_for_entry(
    pre_program,
    entry_t: Transition,
    end_state: str,
) -> Transition | None:
    candidates = [
        t
        for t in pre_program.transitions
        if t.src == entry_t.src and t.tgt == end_state
    ]
    if len(candidates) == 0:
        return None
    if len(candidates) == 1:
        return candidates[0]

    exact = [t for t in candidates if str(t.condition) == str(entry_t.condition)]
    if len(exact) == 1:
        return exact[0]
    if len(exact) > 1:
        return None
    return None


def _nondet_updated_vars(pre_t: Transition) -> list[Variable]:
    return [
        act.left
        for act in pre_t.action
        if isinstance(act.right, NonDeterministic)
    ]


def _deterministic_updated_vars(pre_t: Transition) -> list[Variable]:
    return [
        act.left
        for act in pre_t.action
        if not isinstance(act.right, NonDeterministic)
    ]


def _entry_representation_var(entry_t: Transition, v: Variable) -> Variable:
    int_name = "int_" + v.name
    for act in entry_t.action:
        if (
            str(act.left) == int_name
            and str(act.right) == str(v)
        ):
            return Variable(int_name)
    return v


def _minigame_representation_var(
    post_program, start_state: str, entry_t: Transition, v: Variable
) -> Variable:
    int_v = Variable("int_" + v.name)
    if str(int_v) not in post_program.symbol_table:
        return _entry_representation_var(entry_t, v)

    internal = [
        t
        for t in post_program.transitions
        if t.src == start_state and t.tgt == start_state
    ]
    if any(str(act.left) == str(int_v) for t in internal for act in t.action):
        return int_v

    if any(str(act.left) == str(int_v) for act in entry_t.action):
        return int_v

    return _entry_representation_var(entry_t, v)


def _pre_capability(pre_t: Transition, v: Variable, symbol_table: dict) -> dict[str, bool]:
    rel = conjunct_formula_set([pre_t.condition] + list(pre_t.pred_upgrades))
    vn = _next(v)
    if symbol_table[str(v)] == BOOLEAN:
        return {
            "to_true": sat(conjunct(rel, vn), symbol_table),
            "to_false": sat(conjunct(rel, neg(vn)), symbol_table),
        }
    return {
        "inc": sat(conjunct(rel, BiOp(vn, ">", v)), symbol_table),
        "dec": sat(conjunct(rel, BiOp(vn, "<", v)), symbol_table),
    }


def _minigame_capability(
    post_program, start_state: str, rep_v: Variable, symbol_table: dict
) -> dict[str, bool]:
    step_transitions = [
        t
        for t in post_program.transitions
        if t.src == start_state and any(str(a.left) == str(rep_v) for a in t.action)
    ]
    if len(step_transitions) == 0:
        if symbol_table[str(rep_v)] == BOOLEAN:
            return {"to_true": False, "to_false": False}
        return {"inc": False, "dec": False}
    rels = [_transition_step_formula(t) for t in step_transitions]
    rep_n = _next(rep_v)
    if symbol_table[str(rep_v)] == BOOLEAN:
        return {
            "to_true": any(sat(conjunct(r, rep_n), symbol_table) for r in rels),
            "to_false": any(sat(conjunct(r, neg(rep_n)), symbol_table) for r in rels),
        }
    return {
        "inc": any(sat(conjunct(r, BiOp(rep_n, ">", rep_v)), symbol_table) for r in rels),
        "dec": any(sat(conjunct(r, BiOp(rep_n, "<", rep_v)), symbol_table) for r in rels),
    }


def _expected_exit_formula(
    pre_t: Transition,
    rep_map: dict[str, Variable],
) -> tuple:
    replacements = {}
    for v in _nondet_updated_vars(pre_t):
        replacements[_next(v)] = rep_map.get(str(v), v)

    expected = conjunct_formula_set(pre_t.pred_upgrades)
    if len(replacements) > 0:
        expected = expected.replace_formulas(replacements)
    return expected


def _minigame_manages_rep_var(post_program, start_state: str, rep_v: Variable) -> bool:
    rep_name = str(rep_v)
    for t in post_program.transitions:
        if t.src != start_state:
            continue
        for act in t.action:
            if str(act.left) != rep_name:
                continue
            if str(act.right) != rep_name:
                return True
    return False


def _primed_base_vars_in_pred_upgrades(pre_t: Transition) -> list[Variable]:
    out: dict[str, Variable] = {}
    for p in pre_t.pred_upgrades:
        for v in p.variablesin():
            if isinstance(v, Variable) and v.is_next():
                base = v.prev_rep()
                out[str(base)] = base
    return list(out.values())


def _formula_read_var_names(formula) -> set[str]:
    out = set()
    if formula is None or not hasattr(formula, "variablesin"):
        return out
    for v in formula.variablesin():
        if not isinstance(v, Variable):
            continue
        base = v.prev_rep() if v.is_next() else v
        out.add(str(base))
    return out


def _collect_issy_objective_read_vars(issy_text: str) -> set[str]:
    vars_or_macros, formula_objectives, games = _parse_issy_raw(issy_text)
    del vars_or_macros, games
    out = set()
    for f in formula_objectives:
        out |= _formula_read_var_names(f)
    return out


def _transition_read_write_sets(t: Transition) -> tuple[set[str], set[str]]:
    reads = set()
    kills = set()
    reads |= _formula_read_var_names(t.condition)
    for p in t.pred_upgrades:
        reads |= _formula_read_var_names(p)
    for a in t.action:
        lhs = str(a.left)
        if not isinstance(a.right, NonDeterministic):
            # Identity updates (x := x) should propagate dependency forward,
            # not count as an immediate read/kill of x.
            if str(a.right) == lhs:
                continue
            reads |= _formula_read_var_names(a.right)
        kills.add(lhs)
    for o in t.output:
        if isinstance(o, Variable):
            base = o.prev_rep() if o.is_next() else o
            reads.add(str(base))
        elif hasattr(o, "variablesin"):
            reads |= _formula_read_var_names(o)
    return reads, kills


def _compute_var_may_matter_map(
    post_program,
    var_name: str,
    outgoing_by_state: dict[str, list[Transition]],
    tr_rw_cache: dict[int, tuple[set[str], set[str]]],
    objective_read_vars: set[str],
) -> dict[str, bool]:
    states = [str(s) for s in post_program.states]
    may_matter = {s: (var_name in objective_read_vars) for s in states}
    changed = True
    while changed:
        changed = False
        for s in states:
            cur = may_matter[s]
            if cur:
                continue
            for t in outgoing_by_state.get(s, []):
                reads, kills = tr_rw_cache[id(t)]
                if var_name in reads:
                    may_matter[s] = True
                    changed = True
                    break
                if var_name in kills:
                    continue
                if may_matter.get(str(t.tgt), False):
                    may_matter[s] = True
                    changed = True
                    break
    return may_matter


def _conditions_equivalent(left, right, symbol_table: dict[str, str]) -> bool:
    if str(left) == str(right):
        return True
    return is_tautology(implies(left, right), symbol_table) and is_tautology(
        implies(right, left), symbol_table
    )


def _find_action_for_lhs(t: Transition, lhs_name: str):
    for a in t.action:
        if str(a.left) == lhs_name:
            return a
    return None


def _is_bool_nondet_replaced_by_fresh_controller_choice(
    lhs_name: str,
    rhs_formula,
    post_t: Transition,
    post_program,
    con_prop_names: set[str],
) -> bool:
    if post_program.symbol_table.get(lhs_name) != BOOLEAN:
        return False
    rhs_vars = _formula_read_var_names(rhs_formula)
    if len(rhs_vars) == 0:
        return False
    if any(v not in con_prop_names for v in rhs_vars):
        return False

    guard_vars = _formula_read_var_names(post_t.condition)
    if any(v in guard_vars for v in rhs_vars):
        return False

    for a in post_t.action:
        if str(a.left) == lhs_name:
            continue
        if isinstance(a.right, NonDeterministic):
            continue
        rhs_vars_other = _formula_read_var_names(a.right)
        if any(v in rhs_vars_other for v in rhs_vars):
            return False
    return True


def _direct_nondet_elision_preserved(
    pre_t: Transition,
    post_t: Transition,
    canonical_tgt: str,
    post_program,
    outgoing_by_state: dict[str, list[Transition]],
    tr_rw_cache: dict[int, tuple[set[str], set[str]]],
    objective_read_vars: set[str],
    may_matter_cache: dict[str, dict[str, bool]],
    con_prop_names: set[str],
) -> bool:
    if str(post_t.tgt) != canonical_tgt:
        return False

    nondet_elided_vars = []
    bool_choice_preserved = False
    for pre_a in pre_t.action:
        lhs = str(pre_a.left)
        post_a = _find_action_for_lhs(post_t, lhs)
        if post_a is None:
            return False
        if isinstance(pre_a.right, NonDeterministic):
            if isinstance(post_a.right, NonDeterministic):
                continue
            if str(post_a.right) == lhs:
                nondet_elided_vars.append(lhs)
                continue
            if _is_bool_nondet_replaced_by_fresh_controller_choice(
                lhs, post_a.right, post_t, post_program, con_prop_names
            ):
                bool_choice_preserved = True
                continue
            return False
        if isinstance(post_a.right, NonDeterministic):
            return False
        if str(post_a.right) != str(pre_a.right):
            return False

    if len(nondet_elided_vars) == 0 and not bool_choice_preserved:
        return False

    for v in nondet_elided_vars:
        if v not in may_matter_cache:
            may_matter_cache[v] = _compute_var_may_matter_map(
                post_program,
                v,
                outgoing_by_state,
                tr_rw_cache,
                objective_read_vars,
            )
        if may_matter_cache[v].get(canonical_tgt, False):
            return False
    return True


def _canonical_pre_state_for_post(
    state_name: str,
    post_states: set[str],
    has_lose: bool,
) -> str:
    if state_name in post_states:
        return state_name
    if has_lose:
        # Some post-processing phases collapse certain sink regions into 'lose'.
        return "lose"
    return state_name


def check_cross_product_minigame_transition_sanity_from_text(
    issy_text: str,
    issy_name: str = "issy_input",
) -> MinigameTransitionSanityReport:
    pre_program, post_program, _ = _build_pre_post_cross_product_programs(
        issy_text,
        issy_name,
    )
    capability_failures: list[str] = []
    exit_failures: list[str] = []
    transition_preservation_failures: list[str] = []
    unsupported: list[str] = []

    pre_action_lhs = {str(a.left) for t in pre_program.transitions for a in t.action}
    post_states = set(str(s) for s in post_program.states)
    has_lose = "lose" in post_states
    objective_read_vars = _collect_issy_objective_read_vars(issy_text)
    con_prop_names = {str(v) for v, _ in post_program.con_events}
    outgoing_by_state: dict[str, list[Transition]] = {}
    tr_rw_cache: dict[int, tuple[set[str], set[str]]] = {}
    for tr in post_program.transitions:
        outgoing_by_state.setdefault(str(tr.src), []).append(tr)
        tr_rw_cache[id(tr)] = _transition_read_write_sets(tr)
    may_matter_cache: dict[str, dict[str, bool]] = {}

    entry_transitions = [
        t
        for t in post_program.transitions
        if _is_minigame_state_name(t.tgt) and not _is_minigame_state_name(t.src)
    ]

    post_signatures = {
        _projected_transition_signature(t, pre_action_lhs)
        for t in post_program.transitions
    }
    post_lose_relaxed_signatures = {
        _lose_relaxed_signature_with_states(t, str(t.src), str(t.tgt))
        for t in post_program.transitions
        if str(t.src) == "lose" or str(t.tgt) == "lose"
    }
    post_lose_transitions = [
        t
        for t in post_program.transitions
        if str(t.src) == "lose" or str(t.tgt) == "lose"
    ]
    for t in pre_program.transitions:
        sig = _projected_transition_signature(t, pre_action_lhs)
        canonical_src = _canonical_pre_state_for_post(str(t.src), post_states, has_lose)
        canonical_tgt = _canonical_pre_state_for_post(str(t.tgt), post_states, has_lose)
        sig_canonical = _projected_transition_signature_with_states(
            t,
            pre_action_lhs,
            canonical_src,
            canonical_tgt,
        )
        sig_lose_relaxed = _lose_relaxed_signature_with_states(
            t,
            canonical_src,
            canonical_tgt,
        )
        needs_lose_relaxed = canonical_src != str(t.src) or canonical_tgt != str(t.tgt)

        lose_semantically_preserved = False
        if needs_lose_relaxed:
            lose_semantically_preserved = any(
                _lose_transition_semantically_preserved(
                    t,
                    post_t,
                    canonical_src,
                    canonical_tgt,
                    post_program.symbol_table,
                )
                for post_t in post_lose_transitions
            )

        preserved_directly = (
            sig in post_signatures
            or sig_canonical in post_signatures
            or (
                needs_lose_relaxed
                and (
                    sig_lose_relaxed in post_lose_relaxed_signatures
                    or lose_semantically_preserved
                )
            )
        )
        if preserved_directly:
            continue

        if canonical_tgt == "lose" and _lose_target_preserved_ignoring_actions(
            t,
            post_program,
            canonical_src,
            post_program.symbol_table,
        ):
            continue

        direct_candidates = [
            pt
            for pt in post_program.transitions
            if str(pt.src) == canonical_src
            and str(pt.tgt) == canonical_tgt
            and _conditions_equivalent(
                t.condition, pt.condition, post_program.symbol_table
            )
        ]
        if any(
            _direct_nondet_elision_preserved(
                t,
                pt,
                canonical_tgt,
                post_program,
                outgoing_by_state,
                tr_rw_cache,
                objective_read_vars,
                may_matter_cache,
                con_prop_names,
            )
            for pt in direct_candidates
        ):
            continue

        candidate_entries = [
            e
            for e in entry_transitions
            if str(e.src) == canonical_src and _minigame_end_state(str(e.tgt)) == canonical_tgt
        ]
        if len(candidate_entries) == 0:
            transition_preservation_failures.append(
                "Missing preserved transition in post model:\n"
                + f"  src={t.src}, tgt={t.tgt}\n"
                + f"  cond={t.condition}\n"
                + "  action=["
                + ", ".join(str(a) for a in t.action)
                + "]"
            )
            continue

        pre_nd_vars = _nondet_updated_vars(t)
        primed_base_vars = _primed_base_vars_in_pred_upgrades(t)
        pred_rel = conjunct_formula_set(t.pred_upgrades)
        any_entry_valid = False
        for entry_t in candidate_entries:
            start_state = entry_t.tgt
            end_state = _minigame_end_state(start_state)
            rep_map: dict[str, Variable] = {}
            entry_valid = True

            for v in pre_nd_vars:
                rep_map[str(v)] = _minigame_representation_var(
                    post_program, start_state, entry_t, v
                )

            for v in primed_base_vars:
                if str(v) not in pre_program.symbol_table:
                    continue
                if pre_program.symbol_table[str(v)] == BOOLEAN:
                    continue

                rep_v = rep_map.get(
                    str(v),
                    _minigame_representation_var(post_program, start_state, entry_t, v),
                )
                if str(rep_v) not in post_program.symbol_table:
                    unsupported.append(
                        f"{entry_t.src}->{start_state}: representation variable {rep_v} not in post symbol table."
                    )
                    entry_valid = False
                    break
                if not _minigame_manages_rep_var(post_program, start_state, rep_v):
                    capability_failures.append(
                        f"{entry_t.src}->{start_state} var={v} ({rep_v}) not managed by minigame."
                    )
                    entry_valid = False
                    break

                pre_cap = _pre_capability(t, v, pre_program.symbol_table)
                post_cap = _minigame_capability(
                    post_program, start_state, rep_v, post_program.symbol_table
                )
                for kind, required in pre_cap.items():
                    if required and not post_cap.get(kind, False):
                        capability_failures.append(
                            f"{entry_t.src}->{start_state} var={v} ({rep_v}) missing capability '{kind}'."
                        )
                        entry_valid = False

                vn = _next(v)
                if post_cap.get("inc", False) and not post_cap.get("dec", False):
                    if not is_tautology(
                        implies(pred_rel, BiOp(vn, ">", v)),
                        pre_program.symbol_table,
                    ):
                        capability_failures.append(
                            f"{entry_t.src}->{start_state} var={v}: minigame allows only inc but pred_upgrades do not imply {vn} > {v}."
                        )
                        entry_valid = False
                if post_cap.get("dec", False) and not post_cap.get("inc", False):
                    if not is_tautology(
                        implies(pred_rel, BiOp(vn, "<", v)),
                        pre_program.symbol_table,
                    ):
                        capability_failures.append(
                            f"{entry_t.src}->{start_state} var={v}: minigame allows only dec but pred_upgrades do not imply {vn} < {v}."
                        )
                        entry_valid = False

            expected_exit = _expected_exit_formula(t, rep_map)
            if any(v.is_next() for v in expected_exit.variablesin()):
                unsupported.append(
                    f"{entry_t.src}->{start_state}: exit formula still contains next vars after substitution: {expected_exit}"
                )
                entry_valid = False
                continue

            exit_transitions = [
                et
                for et in post_program.transitions
                if et.src == start_state and et.tgt == end_state
            ]
            if len(exit_transitions) == 0:
                exit_failures.append(
                    f"{entry_t.src}->{start_state}: no exit transition to {end_state}."
                )
                entry_valid = False
                continue

            exit_guard = disjunct_formula_set(et.condition for et in exit_transitions)
            projected_exit_guard = _qe_exists_controller_bool_vars(
                exit_guard,
                post_program.symbol_table,
                list(post_program.con_events),
            )
            if not is_tautology(
                implies(expected_exit, projected_exit_guard),
                post_program.symbol_table,
            ):
                exit_failures.append(
                    f"{entry_t.src}->{start_state}: existentially-projected exit guard does not cover expected exit condition.\n"
                    f"  projected_exit_guard: {projected_exit_guard}\n"
                    f"  expected: {expected_exit}"
                )
                entry_valid = False

            if not sat(
                conjunct(projected_exit_guard, expected_exit),
                post_program.symbol_table,
            ):
                exit_failures.append(
                    f"{entry_t.src}->{start_state}: projected exit guard is incompatible with expected exit condition.\n"
                    f"  projected_exit_guard: {projected_exit_guard}\n"
                    f"  expected: {expected_exit}"
                )
                entry_valid = False

            if entry_valid:
                any_entry_valid = True
                break

        if not any_entry_valid:
            transition_preservation_failures.append(
                "Missing preserved transition/minigame representation in post model:\n"
                + f"  src={t.src}, tgt={t.tgt}\n"
                + f"  cond={t.condition}\n"
                + "  action=["
                + ", ".join(str(a) for a in t.action)
                + "]"
            )

    ok = (
        len(capability_failures) == 0
        and len(exit_failures) == 0
        and len(transition_preservation_failures) == 0
    )
    return MinigameTransitionSanityReport(
        ok=ok,
        capability_failures=capability_failures,
        exit_failures=exit_failures,
        transition_preservation_failures=transition_preservation_failures,
        unsupported=unsupported,
    )


def check_cross_product_minigame_transition_sanity_from_file(
    issy_path: str,
) -> MinigameTransitionSanityReport:
    issy_file = Path(issy_path)
    return check_cross_product_minigame_transition_sanity_from_text(
        issy_file.read_text(),
        issy_name=issy_file.name,
    )


def _main():
    parser = argparse.ArgumentParser(
        description=(
            "SMT sanity checks for cross-product transitions replaced by minigames."
        )
    )
    parser.add_argument("--issy", required=True, help="Path to .issy file")
    args = parser.parse_args()

    report = check_cross_product_minigame_transition_sanity_from_file(args.issy)
    print("ok:", report.ok)
    print("capability_failures:", len(report.capability_failures))
    for f in report.capability_failures:
        print(" -", f)
    print("exit_failures:", len(report.exit_failures))
    for f in report.exit_failures:
        print(" -", f)
    print("transition_preservation_failures:", len(report.transition_preservation_failures))
    for f in report.transition_preservation_failures:
        print(" -", f)
    print("unsupported:", len(report.unsupported))
    for f in report.unsupported:
        print(" -", f)

    if not report.ok:
        raise SystemExit(1)


if __name__ == "__main__":
    _main()
