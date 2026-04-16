import itertools
import logging
from dataclasses import dataclass

import config
from analysis.smt_checker import quantifier_elimination
from parsing.string_to_ltlmt import massage_ltl
from parsing.util.issy.reductions.ltl.formula_utils import (
    _TEMPORAL_OPS,
    formula_only_assumptions_are_initial_or_none,
    is_canonical,
)
from parsing.util.issy.reductions.ltl.guarantee_transition_extractor import (
    IssyGuaranteeTransitionExtractor,
)
from parsing.util.issy.reductions.ltl.spot_update_restrictions import (
    RestrictionScanContext,
    UpdateRestrictionResult,
    derive_restricted_equality_update_choices,
    format_spot_update_restriction_result,
    infer_spot_update_restrictions,
    prepare_restriction_scan_context,
)
from parsing.util.issy.reductions.transition_utils import (
    _build_formula_update_predicate_guard_replacement,
    _restricted_updates_are_pairwise_mutually_exclusive,
)
from parsing.util.game_transition_utils import determinise
from parsing.util.issy.issy_optimisation_reporting import (
    record_optimisation as _record_optimisation,
    record_optimisation_detail as _record_optimisation_detail,
)
from parsing.util.partitioned_update_chain import (
    _canonical_update_predicate_keys,
    build_partitioned_update_chain,
    build_update_predicate_guard_replacements,
)
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    extract_initial_formula,
    fnode_to_formula,
    implies,
    is_tautology,
    neg,
    sat,
    simplify_formula_with_math,
    true,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from pysmt.shortcuts import Exists, Not, Symbol
from pysmt.typing import BOOL, INT


@dataclass(frozen=True)
class _TransitionFragmentRule:
    guard: Formula
    updates: tuple[Update, ...]


def _derive_partial_equality_choices(
    var_to_next_preds: dict[str, list[Formula]],
) -> tuple[dict[str, list[Formula]], set[str]]:
    debug = config.Config.getConfig().debug

    choices: dict[str, list[Formula]] = {}
    nondet_complement_vars: set[str] = set()
    for var_name, preds in sorted(var_to_next_preds.items()):
        rhs_by_key: dict[str, Formula] = {}
        saw_non_equality = False
        for p in preds:
            if debug:
                if not (
                    isinstance(p, BiOp) and is_canonical(p.left, p.right, var_name)
                ):
                    raise ValueError(
                        f"Unsupported non-canonical update predicate for variable '{var_name}': {p}"
                    )
            if not isinstance(p, BiOp) or str(p.op) != "=":
                saw_non_equality = True
                continue
            rhs = p.right
            rhs_by_key[str(rhs)] = rhs
        if len(rhs_by_key) > 0:
            choices[var_name] = [
                rhs for _, rhs in sorted(rhs_by_key.items(), key=lambda item: item[0])
            ]
        if saw_non_equality or len(rhs_by_key) == 0:
            nondet_complement_vars.add(var_name)
    return choices, nondet_complement_vars


def _complete_raw_transitions_with_lose(raw_transitions, symbol_table):
    lose_transitions = []
    for src, trans in raw_transitions.items():
        no_trans_triggered = neg(disjunct_formula_set(t.condition for t in trans))
        if sat(no_trans_triggered, symbol_table):
            lose_transitions.append(Transition(src, no_trans_triggered, [], [], "lose"))
    return lose_transitions


def _guarantee_extraction_would_avoid_minigames(extraction_result, state_vars) -> bool:
    if extraction_result is None or not extraction_result.applied:
        return False
    required_vars = set(state_vars)
    if len(required_vars) == 0:
        return True
    for tr in extraction_result.transitions:
        updated_vars = {
            u.left for u in tr.action if not isinstance(u.right, NonDeterministic)
        }
        if not required_vars.issubset(updated_vars):
            return False
    return True


def _formula_contains_temporal_operator(q: Formula) -> bool:
    return len(_TEMPORAL_OPS.intersection(q.ops_used())) > 0


def _collect_state_eventually_goals(formula: Formula) -> list[Formula] | None:
    """Collect top-level F(goal) formulas, where goal is a propositional formula."""

    goals = {}

    def _walk(q: Formula) -> bool:
        if isinstance(q, UniOp):
            if q.op == "F":
                goal = q.right
                if not _formula_contains_temporal_operator(goal):
                    goals[str(goal)] = goal
                return True
            elif q.op in {"G", "X"}:
                return False
            return _walk(q.right)
        if isinstance(q, BiOp):
            if q.op in {"U", "R", "W", "M"}:
                return False
            return _walk(q.left) and _walk(q.right)
        return True

    if not _walk(formula):
        return None
    return [goals[k] for k in sorted(goals.keys())]


def _derive_goal_scoped_update_restrictions_from_guarantee_extraction(
    extraction_result,
    rewritten_objectives: list[Formula],
    state_vars: list[Variable],
    symbol_table: dict,
    base_scan_context: RestrictionScanContext,
):
    if extraction_result is None or not extraction_result.applied:
        return None
    if len(rewritten_objectives) == 0:
        return None

    goals = []
    for obj in rewritten_objectives:
        collected = _collect_state_eventually_goals(obj)
        if collected is None:
            return None
        goals.extend(collected)
    goals_map = {str(g): g for g in goals}
    goals = [goals_map[k] for k in sorted(goals_map.keys())]
    if len(goals) == 0:
        return None

    state_var_names = {str(v) for v in state_vars}
    transitions_with_updates = []
    for tr in extraction_result.transitions:
        if any(
            str(u.left) in state_var_names and not isinstance(u.right, NonDeterministic)
            for u in tr.action
        ):
            transitions_with_updates.append(tr)
    if len(transitions_with_updates) == 0:
        return None

    for goal in goals:
        for tr in transitions_with_updates:
            if sat(conjunct(goal, tr.condition), symbol_table):
                return None

    restricted_var_to_guard_terms = {}
    var_to_rhs = {}
    for tr in transitions_with_updates:
        for upd in tr.action:
            var_name = str(upd.left)
            if var_name not in state_var_names:
                continue
            if isinstance(upd.right, NonDeterministic):
                continue
            rhs = upd.right
            pred = BiOp(Variable(var_name + "'"), "=", rhs)
            pred_key = str(pred)
            var_to_rhs.setdefault(var_name, {})[str(rhs)] = rhs
            restricted_var_to_guard_terms.setdefault(var_name, {}).setdefault(
                pred_key, {"pred": pred, "guards": []}
            )["guards"].append(tr.condition)

    if len(restricted_var_to_guard_terms) == 0:
        return None

    restricted_var_to_guard = {}
    restricted_var_to_goal = {}
    restricted_var_to_preds = {}
    equality_choice_map = {}
    for var_name, pred_entry_map in sorted(restricted_var_to_guard_terms.items()):
        pred_entries = [pred_entry_map[k] for k in sorted(pred_entry_map.keys())]
        preds = [entry["pred"] for entry in pred_entries]
        if len(preds) == 0:
            continue
        restricted_var_to_preds[var_name] = preds
        equality_choice_map[var_name] = [
            rhs for _, rhs in sorted(var_to_rhs[var_name].items(), key=lambda kv: kv[0])
        ]
        restricted_var_to_guard[var_name] = disjunct_formula_set(
            disjunct_formula_set(entry["guards"]) for entry in pred_entries
        )
        restricted_var_to_goal[var_name] = disjunct_formula_set(goals)

    if len(restricted_var_to_preds) == 0:
        return None

    result = UpdateRestrictionResult(
        scan_context=base_scan_context,
        restricted_var_to_guard=restricted_var_to_guard,
        goal_scoped_restrictions=True,
        restricted_var_to_goal=restricted_var_to_goal,
    )
    return result, equality_choice_map, restricted_var_to_preds


def _formula_contains_next_vars(formula: Formula) -> bool:
    return any(v for v in formula.variablesin() if v.is_next())


def _is_state_guard_without_next(q: Formula) -> bool:
    if any(op in {"X", "F", "G", "U", "W", "R", "M"} for op in q.ops_used()):
        return False
    return not any(v for v in q.variablesin() if v.is_next())


def _extract_eq_updates_from_formula(
    q: Formula,
    *,
    allowed_state_var_names: set[str],
    symbol_table,
) -> dict[str, Formula] | None:
    if isinstance(q, Value):
        return {} if q.is_true() else None
    if isinstance(q, BiOp) and str(q.op) == "&":
        left = _extract_eq_updates_from_formula(
            q.left,
            allowed_state_var_names=allowed_state_var_names,
            symbol_table=symbol_table,
        )
        if left is None:
            return None
        right = _extract_eq_updates_from_formula(
            q.right,
            allowed_state_var_names=allowed_state_var_names,
            symbol_table=symbol_table,
        )
        if right is None:
            return None
        out = dict(left)
        for var_name, rhs in right.items():
            if var_name not in out:
                out[var_name] = rhs
                continue
            if not is_tautology(BiOp(out[var_name], "=", rhs), symbol_table):
                return None
        return out
    if not isinstance(q, BiOp) or str(q.op) != "=":
        return None

    left = q.left
    right = q.right
    lhs = left
    rhs = right
    if isinstance(right, Variable) and right.is_next():
        lhs = right
        rhs = left
    if not isinstance(lhs, Variable) or not lhs.is_next():
        return None
    var_name = lhs.prev_rep().name
    if var_name not in allowed_state_var_names:
        return None
    rhs = rhs
    if any(v for v in rhs.variablesin() if v.is_next()):
        return None
    if any(op in {"X", "F", "G", "U", "W", "R", "M"} for op in rhs.ops_used()):
        return None
    return {var_name: rhs}


def _extract_transition_fragment_rules(
    q: Formula,
    *,
    allowed_state_var_names: set[str],
    symbol_table,
) -> list[_TransitionFragmentRule] | None:
    if isinstance(q, BiOp) and str(q.op) == "&":
        left = _extract_transition_fragment_rules(
            q.left,
            allowed_state_var_names=allowed_state_var_names,
            symbol_table=symbol_table,
        )
        right = _extract_transition_fragment_rules(
            q.right,
            allowed_state_var_names=allowed_state_var_names,
            symbol_table=symbol_table,
        )
        if left is None or right is None:
            return None
        return left + right
    if not isinstance(q, UniOp) or q.op != "G":
        return None

    body = q.right
    if isinstance(body, BiOp) and str(body.op) == "->":
        guard = body.left
        updates_formula = body.right
    else:
        guard = true()
        updates_formula = body
    if not _is_state_guard_without_next(guard):
        return None

    updates_map = _extract_eq_updates_from_formula(
        updates_formula,
        allowed_state_var_names=allowed_state_var_names,
        symbol_table=symbol_table,
    )
    if updates_map is None:
        return None
    updates = tuple(
        Update(Variable(var_name), rhs)
        for var_name, rhs in sorted(updates_map.items(), key=lambda item: item[0])
    )
    return [_TransitionFragmentRule(guard=guard, updates=updates)]


def _flatten_conjuncts_for_transition_fragment(q: Formula) -> list[Formula]:
    if isinstance(q, BiOp) and str(q.op) == "&":
        return _flatten_conjuncts_for_transition_fragment(
            q.left
        ) + _flatten_conjuncts_for_transition_fragment(q.right)
    return [q]


def _extract_mutually_exclusive_transition_fragment(
    formula_objectives: list[Formula],
    *,
    state_vars: list[Variable],
    symbol_table,
) -> tuple[list[_TransitionFragmentRule], list[Formula]] | None:
    allowed_state_var_names = {str(v) for v in state_vars}
    rules: list[_TransitionFragmentRule] = []
    leftover_objectives: list[Formula] = []

    for objective in formula_objectives:
        candidate = objective
        if isinstance(candidate, BiOp) and str(candidate.op) == "->":
            antecedent = candidate.left
            antecedent_init = extract_initial_formula(antecedent)
            if (isinstance(antecedent, Value) and antecedent.is_true()) or (
                antecedent_init is not None and str(antecedent_init) == str(antecedent)
            ):
                candidate = candidate.right

        if _formula_contains_next_vars(candidate):
            conjuncts = (
                _flatten_conjuncts_for_transition_fragment(candidate)
                if isinstance((candidate), BiOp) and str((candidate).op) == "&"
                else [candidate]
            )
            for conjunct_formula in conjuncts:
                conjunct_formula = conjunct_formula
                if not _formula_contains_next_vars(conjunct_formula):
                    leftover_objectives.append(conjunct_formula)
                    continue
                extracted = _extract_transition_fragment_rules(
                    conjunct_formula,
                    allowed_state_var_names=allowed_state_var_names,
                    symbol_table=symbol_table,
                )
                if extracted is None:
                    return None
                rules.extend(extracted)
        else:
            leftover_objectives.append(candidate)

    if len(rules) == 0:
        return None
    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            if sat(conjunct(rules[i].guard, rules[j].guard), symbol_table):
                return None
    return rules, leftover_objectives


def _resolve_formula_only_fast_path_strategy(
    *,
    name_str,
    inputs,
    state_vars,
    symbol_table,
    new_con_props,
    formula_objectives_no_snapshot,
    optimisation_summary: dict,
):
    def _partition_nondet_complements(
        eq_choices: dict[str, list[Formula]],
        active_result: UpdateRestrictionResult,
        partial_nondet_vars: set[str],
    ) -> set[str]:
        nondet = set(partial_nondet_vars)
        unrestricted_eq_vars = set(eq_choices.keys()).difference(
            set(active_result.restricted_var_to_guard.keys())
        )
        nondet.update(unrestricted_eq_vars)
        return nondet

    def _capture_fast_path_candidates(
        restriction_result: UpdateRestrictionResult,
    ) -> tuple[
        tuple[dict[str, list[Formula]], dict[str, list[Formula]]] | None,
        tuple[dict[str, list[Formula]], set[str], UpdateRestrictionResult] | None,
    ]:
        if len(restriction_result.restricted_var_to_guard) == 0:
            return None, None
        equality_choice_map = derive_restricted_equality_update_choices(
            restriction_result
        )
        if equality_choice_map is None:
            return None, None
        restricted_var_to_preds = {
            var_name: restriction_result.scan_context.var_to_next_preds[var_name]
            for var_name in restriction_result.restricted_var_to_guard.keys()
            if var_name in restriction_result.scan_context.var_to_next_preds
        }
        explicit_candidate = None
        if _restricted_updates_are_pairwise_mutually_exclusive(
            restricted_var_to_preds,
            symbol_table,
        ):
            explicit_candidate = (equality_choice_map, restricted_var_to_preds)

        partition_candidate = None
        if has_fast_path_objective:
            _, partial_restricted_nondet_vars = _derive_partial_equality_choices(
                restricted_var_to_preds
            )
            nondet_complement_var_names = _partition_nondet_complements(
                equality_choice_map,
                restriction_result,
                partial_restricted_nondet_vars,
            )
            partition_candidate = (
                equality_choice_map,
                nondet_complement_var_names,
                restriction_result,
            )
        return explicit_candidate, partition_candidate

    curr_state_vars = []
    has_fast_path_objective = len(formula_objectives_no_snapshot) > 0
    if len(formula_objectives_no_snapshot) > 1:
        formula_objective_for_fast_path_check = conjunct_formula_set(
            formula_objectives_no_snapshot
        )
    elif len(formula_objectives_no_snapshot) == 1:
        formula_objective_for_fast_path_check = formula_objectives_no_snapshot[0]
    else:
        formula_objective_for_fast_path_check = conjunct_formula_set([])

    transition_fragment_candidate = _extract_mutually_exclusive_transition_fragment(
        formula_objectives=formula_objectives_no_snapshot,
        state_vars=state_vars,
        symbol_table=symbol_table,
    )
    use_transition_fragment_fast_path = transition_fragment_candidate is not None
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "transition_fragment_fast_path_applied",
        1 if use_transition_fragment_fast_path else 0,
    )
    if use_transition_fragment_fast_path:
        transition_fragment_rules, transition_fragment_objectives = (
            transition_fragment_candidate
        )
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "partition_chain_fast_path_applied",
            0,
        )
        _record_optimisation_detail(
            optimisation_summary,
            "formula_only",
            "transition_fragment_fast_path_vars",
            ", ".join(sorted(str(v) for v in state_vars)),
        )
        return _build_formula_only_transition_fragment_program(
            name_str=name_str,
            inputs=inputs,
            state_vars=state_vars,
            curr_state_vars=curr_state_vars,
            symbol_table=symbol_table,
            new_con_props=new_con_props,
            rules=transition_fragment_rules,
            formula_objectives=transition_fragment_objectives,
            optimisation_summary=optimisation_summary,
        )

    formula_objectives = list(formula_objectives_no_snapshot)
    input_snapshot_updates = []

    restriction_scan_context = prepare_restriction_scan_context(
        formula_objective_for_fast_path_check,
        allowed_next_var_names={str(v) for v in state_vars},
        relax_initial_implication_assumptions=True,
    )
    spot_restriction_result = infer_spot_update_restrictions(restriction_scan_context)
    logging.info(format_spot_update_restriction_result(spot_restriction_result))
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "spot_update_restriction_applied_vars",
        len(spot_restriction_result.restricted_var_to_guard),
    )
    active_spot_restriction_result = spot_restriction_result
    explicit_candidate, partition_candidate = _capture_fast_path_candidates(
        spot_restriction_result
    )

    # Attempt 2: guarantee-derived goal-scoped restrictions
    precomputed_guarantee_extraction_result = None
    allow_guarantee_transition_extraction = (
        formula_only_assumptions_are_initial_or_none(
            list(formula_objectives_no_snapshot)
        )
    )
    if allow_guarantee_transition_extraction:
        extractor = IssyGuaranteeTransitionExtractor(
            symbol_table,
            {str(v) for v in state_vars},
            eval_state="eval",
        )
        precomputed_guarantee_extraction_result = extractor.extract(
            list(formula_objectives_no_snapshot)
        )
        derived_goal_scoped = (
            _derive_goal_scoped_update_restrictions_from_guarantee_extraction(
                precomputed_guarantee_extraction_result,
                list(precomputed_guarantee_extraction_result.rewritten_objectives),
                state_vars,
                symbol_table,
                restriction_scan_context,
            )
        )
        if derived_goal_scoped is not None:
            (
                active_spot_restriction_result,
                equality_choice_map,
                restricted_var_to_preds,
            ) = derived_goal_scoped
            _record_optimisation_detail(
                optimisation_summary,
                "formula_only",
                "guarantee_goal_scoped_partition_restrictions",
                ", ".join(sorted(equality_choice_map.keys())),
            )
            guarantee_explicit_candidate = None
            if _restricted_updates_are_pairwise_mutually_exclusive(
                restricted_var_to_preds,
                symbol_table,
            ):
                guarantee_explicit_candidate = (
                    equality_choice_map,
                    restricted_var_to_preds,
                )
            if explicit_candidate is None:
                explicit_candidate = guarantee_explicit_candidate
            if (
                partition_candidate is None
                and len(equality_choice_map) > 0
                and has_fast_path_objective
            ):
                _, guarantee_partial_nondet_vars = _derive_partial_equality_choices(
                    restricted_var_to_preds
                )
                guarantee_nondet_complement_var_names = _partition_nondet_complements(
                    equality_choice_map,
                    active_spot_restriction_result,
                    guarantee_partial_nondet_vars,
                )
                partition_candidate = (
                    equality_choice_map,
                    guarantee_nondet_complement_var_names,
                    active_spot_restriction_result,
                )
    else:
        logging.info(
            "ISSY guarantee-transition extraction skipped: assumptions are not all initial-state."
        )

    if explicit_candidate is not None:
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "partition_chain_fast_path_applied",
            0,
        )
        candidate_equality_choice_map, candidate_restricted_var_to_preds = (
            explicit_candidate
        )
        return _build_formula_only_explicit_choice_program(
            name_str=name_str,
            inputs=inputs,
            state_vars=state_vars,
            curr_state_vars=curr_state_vars,
            symbol_table=symbol_table,
            new_con_props=new_con_props,
            equality_choice_map=candidate_equality_choice_map,
            restricted_var_to_preds=candidate_restricted_var_to_preds,
            input_snapshot_updates=input_snapshot_updates,
            formula_objectives=formula_objectives,
            optimisation_summary=optimisation_summary,
        )

    if partition_candidate is None:
        all_var_to_next_preds = dict(
            active_spot_restriction_result.scan_context.var_to_next_preds
        )
        fallback_equality_choices, fallback_nondet_vars = (
            _derive_partial_equality_choices(all_var_to_next_preds)
        )
        if len(fallback_equality_choices) > 0 and has_fast_path_objective:
            _record_optimisation_detail(
                optimisation_summary,
                "formula_only",
                "partition_chain_partial_equality_fallback_vars",
                ", ".join(sorted(fallback_equality_choices.keys())),
            )
            fallback_nondet_complement_var_names = _partition_nondet_complements(
                fallback_equality_choices,
                active_spot_restriction_result,
                fallback_nondet_vars,
            )
            partition_candidate = (
                fallback_equality_choices,
                fallback_nondet_complement_var_names,
                active_spot_restriction_result,
            )

    if partition_candidate is not None:
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "partition_chain_fast_path_applied",
            1,
        )
        (
            candidate_equality_choice_map,
            candidate_nondet_complement_var_names,
            candidate_active_spot_restriction_result,
        ) = partition_candidate
        return _build_formula_only_partition_chain_program(
            name_str=name_str,
            inputs=inputs,
            state_vars=state_vars,
            curr_state_vars=curr_state_vars,
            symbol_table=symbol_table,
            new_con_props=new_con_props,
            equality_choice_map=candidate_equality_choice_map,
            nondet_complement_var_names=candidate_nondet_complement_var_names,
            formula_objective_for_fast_path_check=formula_objective_for_fast_path_check,
            active_spot_restriction_result=candidate_active_spot_restriction_result,
            optimisation_summary=optimisation_summary,
        )

    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "partition_chain_fast_path_applied",
        0,
    )
    restricted_guard_by_var = dict(
        active_spot_restriction_result.restricted_var_to_guard
    )
    return _build_formula_only_fallback_program(
        name_str=name_str,
        inputs=inputs,
        state_vars=state_vars,
        curr_state_vars=curr_state_vars,
        symbol_table=symbol_table,
        formula_objectives=formula_objectives,
        new_con_props=new_con_props,
        input_snapshot_updates=input_snapshot_updates,
        restricted_guard_by_var=restricted_guard_by_var,
        active_spot_restriction_result=active_spot_restriction_result,
        spot_restriction_result=spot_restriction_result,
        optimisation_summary=optimisation_summary,
        precomputed_guarantee_extraction_result=precomputed_guarantee_extraction_result,
        allow_guarantee_transition_extraction=allow_guarantee_transition_extraction,
    )


def _record_applied_formula_only_guarantee_extraction(
    guarantee_extraction_result,
    optimisation_summary: dict,
):
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "guarantee_transition_rules_extracted",
        guarantee_extraction_result.extracted_rule_count,
    )
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "guarantee_transition_formulas_removed",
        guarantee_extraction_result.extracted_formula_count,
    )
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "guarantee_transition_partition_transitions",
        len(guarantee_extraction_result.transitions),
    )


def _materialise_formula_only_guarantee_extraction(
    guarantee_extraction_result,
    new_con_props: set,
    symbol_table,
    optimisation_summary: dict,
):
    formula_objectives = list(guarantee_extraction_result.rewritten_objectives)
    if len(guarantee_extraction_result.new_controller_props) > 0:
        new_con_props.update(set(guarantee_extraction_result.new_controller_props))
        for p in guarantee_extraction_result.new_controller_props:
            symbol_table[str(p)] = BOOLEAN
    _record_applied_formula_only_guarantee_extraction(
        guarantee_extraction_result,
        optimisation_summary,
    )
    return formula_objectives


def _qe_equivalent_update_condition(
    lhs: Formula, rhs: Formula, var_name: str, symbol_table
):
    if str(lhs) == str(rhs):
        return true()
    try:
        smt_ty = BOOL if symbol_table.get(var_name) == BOOLEAN else INT
        neq = neg(BiOp(lhs, "=", rhs))
        neq_smt = neq.to_smt(symbol_table)[0]
        quantified = Not(Exists([Symbol(var_name, smt_ty)], neq_smt))
        qe = quantifier_elimination(quantified)
        return simplify_formula_with_math(fnode_to_formula(qe), symbol_table)
    except Exception:
        return simplify_formula_with_math(BiOp(lhs, "=", rhs), symbol_table)


def _transitions_updates_equivalent_under_guard(
    t_left: Transition, t_right: Transition, guard: Formula, symbol_table
) -> bool:
    left_updates = {str(u.left): u.right for u in t_left.action}
    right_updates = {str(u.left): u.right for u in t_right.action}
    if set(left_updates.keys()) != set(right_updates.keys()):
        return False
    for var_name in sorted(left_updates.keys()):
        left_rhs = left_updates[var_name]
        right_rhs = right_updates[var_name]
        if isinstance(left_rhs, NonDeterministic) and isinstance(
            right_rhs, NonDeterministic
        ):
            continue
        if isinstance(left_rhs, NonDeterministic) or isinstance(
            right_rhs, NonDeterministic
        ):
            return False
        eq_cond = _qe_equivalent_update_condition(
            left_rhs,
            right_rhs,
            var_name,
            symbol_table,
        )
        if not is_tautology(implies(guard, eq_cond), symbol_table):
            return False
    return True


def _merge_extracted_transitions_with_qe_equivalent_overlaps(
    transitions: list[Transition], symbol_table
) -> tuple[list[Transition], int]:
    if len(transitions) <= 1:
        return transitions, 0
    out = []
    merged_overlap_regions = 0
    by_src = {}
    for t in transitions:
        by_src.setdefault(str(t.src), []).append(t)

    for src in sorted(by_src.keys()):
        buckets = {}
        for t in by_src[src]:
            key = (
                str(t.tgt),
                tuple(str(o) for o in t.output),
                tuple(sorted(str(p) for p in t.pred_upgrades)),
            )
            buckets.setdefault(key, []).append(t)

        for key in sorted(buckets.keys()):
            work = list(buckets[key])
            changed = True
            while changed:
                changed = False
                for i in range(len(work)):
                    if changed:
                        break
                    for j in range(i + 1, len(work)):
                        t_i = work[i]
                        t_j = work[j]
                        overlap = simplify_formula_with_math(
                            conjunct(t_i.condition, t_j.condition), symbol_table
                        )
                        if not sat(overlap, symbol_table):
                            continue
                        if not _transitions_updates_equivalent_under_guard(
                            t_i, t_j, overlap, symbol_table
                        ):
                            continue

                        left_only = simplify_formula_with_math(
                            conjunct(t_i.condition, neg(t_j.condition)),
                            symbol_table,
                        )
                        right_only = simplify_formula_with_math(
                            conjunct(t_j.condition, neg(t_i.condition)),
                            symbol_table,
                        )
                        replacement = []
                        overlap_t = Transition(
                            t_i.src,
                            overlap,
                            list(t_i.action),
                            list(t_i.output),
                            t_i.tgt,
                        )
                        overlap_t.set_predicate_upgrades(list(t_i.pred_upgrades))
                        replacement.append(overlap_t)
                        if sat(left_only, symbol_table):
                            left_t = Transition(
                                t_i.src,
                                left_only,
                                list(t_i.action),
                                list(t_i.output),
                                t_i.tgt,
                            )
                            left_t.set_predicate_upgrades(list(t_i.pred_upgrades))
                            replacement.append(left_t)
                        if sat(right_only, symbol_table):
                            right_t = Transition(
                                t_j.src,
                                right_only,
                                list(t_j.action),
                                list(t_j.output),
                                t_j.tgt,
                            )
                            right_t.set_predicate_upgrades(list(t_j.pred_upgrades))
                            replacement.append(right_t)
                        work = [
                            t for k, t in enumerate(work) if k not in {i, j}
                        ] + replacement
                        merged_overlap_regions += 1
                        changed = True
                        break
            out.extend(work)

    dedup = {}
    for t in out:
        key = (
            str(t.src),
            str(t.tgt),
            str(t.condition),
            tuple(sorted(str(a) for a in t.action)),
            tuple(sorted(str(o) for o in t.output)),
            tuple(sorted(str(p) for p in t.pred_upgrades)),
        )
        dedup[key] = t
    return [dedup[k] for k in sorted(dedup.keys())], merged_overlap_regions


def _apply_formula_only_guarantee_extraction(
    *,
    formula_objectives,
    state_vars,
    symbol_table,
    new_con_props: set,
    optimisation_summary: dict,
    precomputed_guarantee_extraction_result=None,
    allow_guarantee_transition_extraction: bool,
):
    guarantee_extraction_result = precomputed_guarantee_extraction_result
    if guarantee_extraction_result is None and allow_guarantee_transition_extraction:
        extractor = IssyGuaranteeTransitionExtractor(
            symbol_table,
            {str(v) for v in state_vars},
            eval_state="eval",
        )
        guarantee_extraction_result = extractor.extract(list(formula_objectives))
        if (
            guarantee_extraction_result.applied
            and not _guarantee_extraction_would_avoid_minigames(
                guarantee_extraction_result, state_vars
            )
        ):
            guarantee_extraction_result = None
        if (
            guarantee_extraction_result is not None
            and guarantee_extraction_result.applied
        ):
            formula_objectives = _materialise_formula_only_guarantee_extraction(
                guarantee_extraction_result,
                new_con_props,
                symbol_table,
                optimisation_summary,
            )
        elif (
            guarantee_extraction_result is not None
            and guarantee_extraction_result.skipped_reason is not None
        ):
            logging.info(
                "ISSY guarantee-transition extraction skipped: %s",
                guarantee_extraction_result.skipped_reason,
            )
    elif (
        guarantee_extraction_result is not None and guarantee_extraction_result.applied
    ):
        formula_objectives = _materialise_formula_only_guarantee_extraction(
            guarantee_extraction_result,
            new_con_props,
            symbol_table,
            optimisation_summary,
        )
    return guarantee_extraction_result, formula_objectives


def _build_formula_only_transition_fragment_program(
    *,
    name_str,
    inputs,
    state_vars,
    curr_state_vars,
    symbol_table,
    new_con_props,
    rules: list[_TransitionFragmentRule] | None,
    formula_objectives: list[Formula] | None,
    optimisation_summary: dict,
):
    if rules is None or len(rules) == 0:
        raise Exception(
            "transition-fragment fast path requires non-empty extracted rules"
        )
    if formula_objectives is None:
        formula_objectives = []
    stutter_completion_goal = None
    if len(formula_objectives) == 1:
        only_obj = formula_objectives[0]
        if isinstance(only_obj, UniOp) and only_obj.op == "F":
            candidate_goal = only_obj.right
            if _is_state_guard_without_next(candidate_goal):
                stutter_completion_goal = candidate_goal

    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            if sat(conjunct(rules[i].guard, rules[j].guard), symbol_table):
                raise Exception(
                    "transition-fragment fast path requires mutually-exclusive source guards"
                )

    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "transition_fragment_rules_extracted",
        len(rules),
    )

    program_transitions = []
    for rule in rules:
        updated_vars = {u.left for u in rule.updates}
        actions = list(rule.updates) + [
            Update(v, NonDeterministic()) for v in state_vars if v not in updated_vars
        ]
        program_transitions.append(Transition("eval", rule.guard, actions, [], "eval"))

    covered_guards = [t.condition for t in program_transitions]
    if len(covered_guards) > 0:
        fallback_guard = simplify_formula_with_math(
            neg(disjunct_formula_set(covered_guards)),
            symbol_table,
        )
        if sat(fallback_guard, symbol_table):
            noncovered_is_winning_reachability = False
            if stutter_completion_goal is not None:
                goals_disj = stutter_completion_goal
                noncovered_is_winning_reachability = not sat(
                    conjunct(fallback_guard, neg(goals_disj)),
                    symbol_table,
                )
            fallback_actions = (
                [Update(v, v) for v in state_vars]
                if noncovered_is_winning_reachability
                else [Update(v, NonDeterministic()) for v in state_vars]
            )
            program_transitions.append(
                Transition(
                    "eval",
                    fallback_guard,
                    fallback_actions,
                    [],
                    "eval",
                )
            )
            _record_optimisation(
                optimisation_summary,
                "formula_only",
                "transition_fragment_uncovered_guard_nondet_completion",
                1,
            )

    program = Program(
        name_str,
        {"eval"},
        "eval",
        [(str(v), symbol_table[str(v)]) for v in state_vars + curr_state_vars],
        program_transitions,
        [(v, symbol_table[str(v)]) for v in inputs],
        sorted([(v, BOOLEAN) for v in set(new_con_props)], key=lambda e: str(e[0])),
        preprocess=False,
        emit_state_binary_map=False,
    )
    return program, list(formula_objectives)


def _build_formula_only_partition_chain_program(
    *,
    name_str,
    inputs,
    state_vars,
    curr_state_vars,
    symbol_table,
    new_con_props,
    equality_choice_map,
    nondet_complement_var_names,
    formula_objective_for_fast_path_check,
    active_spot_restriction_result,
    optimisation_summary: dict,
):
    def _is_self_stutter_rhs(var_name: str, rhs: Formula) -> bool:
        return isinstance(rhs, Variable) and str(rhs) == var_name

    stutter_only_var_names = {
        var_name
        for var_name, rhs_choices in equality_choice_map.items()
        if len(rhs_choices) > 0
        and var_name not in nondet_complement_var_names
        and all(_is_self_stutter_rhs(var_name, rhs) for rhs in rhs_choices)
    }
    stutter_only_updates = [
        Update(Variable(var_name), Variable(var_name))
        for var_name in sorted(stutter_only_var_names)
    ]

    updates_by_var = {
        var_name: {Update(Variable(var_name), rhs) for rhs in rhs_choices}
        for var_name, rhs_choices in equality_choice_map.items()
        if var_name not in stutter_only_var_names
    }
    goal_scoped_nondet_vars = (
        set(active_spot_restriction_result.restricted_var_to_goal.keys())
        if active_spot_restriction_result.goal_scoped_restrictions
        else set()
    )
    nondet_complement_vars = set(nondet_complement_var_names)
    nondet_complement_vars.update(goal_scoped_nondet_vars)
    input_var_names = {str(v) for v in inputs}
    pred_upgrade_input_var_names = set()
    for var_name in sorted(nondet_complement_vars):
        for rhs in equality_choice_map.get(var_name, []):
            for dep_var in rhs.variablesin():
                dep_name = str(dep_var)
                if dep_name in input_var_names:
                    pred_upgrade_input_var_names.add(dep_name)
    combine_input_dependent_partitions = len(pred_upgrade_input_var_names) == 0
    if not combine_input_dependent_partitions:
        _record_optimisation_detail(
            optimisation_summary,
            "formula_only",
            "partition_chain_input_partition_merge_blocked_by_pred_upgrade_inputs",
            ", ".join(sorted(pred_upgrade_input_var_names)),
        )
    for var_name in sorted(nondet_complement_vars):
        updates_by_var.setdefault(var_name, set()).add(
            Update(Variable(var_name), NonDeterministic())
        )

    chain = build_partitioned_update_chain(
        updates_by_var,
        inputs,
        state_prefix="c_",
        selector_prefix="formula_con_act_",
        use_curr_input_snapshots=False,
        group_input_dependent_first=combine_input_dependent_partitions,
        use_qe_equivalent_update_guard_fusion=True,
        symbol_table=symbol_table,
    )
    if len(stutter_only_updates) > 0:
        for t in chain.transitions:
            already_updated = {str(a.left) for a in t.action}
            t.action.extend(
                upd
                for upd in stutter_only_updates
                if str(upd.left) not in already_updated
            )
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "partition_chain_dropped_stutter_only_partitions",
            len(stutter_only_updates),
        )

    if len(nondet_complement_vars) > 0:
        deterministic_rhs_by_state_var = {}
        for t in chain.transitions:
            for upd in t.action:
                if str(upd.left) in nondet_complement_vars and not isinstance(
                    upd.right, NonDeterministic
                ):
                    key = (str(t.src), str(upd.left))
                    deterministic_rhs_by_state_var.setdefault(key, {})
                    deterministic_rhs_by_state_var[key][str((upd.right))] = upd.right
        for t in chain.transitions:
            pred_upgrades = list(t.pred_upgrades)
            for upd in t.action:
                if str(upd.left) not in nondet_complement_vars or not isinstance(
                    upd.right, NonDeterministic
                ):
                    continue
                key = (str(t.src), str(upd.left))
                excluded_rhs = deterministic_rhs_by_state_var.get(key, {})
                if len(excluded_rhs) == 0:
                    continue
                next_v = Variable(str(upd.left) + "'")
                pred_upgrades.extend(
                    BiOp(next_v, "!=", rhs)
                    for rhs in sorted(excluded_rhs.values(), key=lambda rr: str(rr))
                )
            if len(pred_upgrades) > 0:
                t.set_predicate_upgrades(pred_upgrades)
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "partition_chain_nondet_complement_transitions",
            len(nondet_complement_vars),
        )

    chain_snapshot_state_vars = sorted(
        list(chain.snapshot_state_vars), key=lambda v: v.name
    )
    for curr_v in chain_snapshot_state_vars:
        curr_name = str(curr_v)
        if curr_name in symbol_table:
            continue
        inp_name = curr_name[5:] if curr_name.startswith("curr_") else None
        if inp_name is not None and inp_name in symbol_table:
            symbol_table[curr_name] = symbol_table[inp_name]
    update_predicate_key_to_guard = dict(chain.update_predicate_key_to_guard)
    for upd in stutter_only_updates:
        for pred_key in _canonical_update_predicate_keys(upd):
            update_predicate_key_to_guard[pred_key] = true()
    pred_to_guard = build_update_predicate_guard_replacements(
        formula_objective_for_fast_path_check,
        update_predicate_key_to_guard,
    )
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "spot_update_predicates_rewritten_to_guards",
        len({str(k) for k in pred_to_guard.keys() if not isinstance(k, MathExpr)}),
    )

    if len(chain.states) > 1:
        formula_objectives = [
            massage_ltl(
                formula_objective_for_fast_path_check,
                Variable(chain.eval_state),
                pred_to_guard,
            )
        ]
    else:
        formula_objectives = [
            formula_objective_for_fast_path_check.replace_formulas(pred_to_guard)
        ]

    formula_only_con_events = {(v, BOOLEAN) for v in new_con_props} | {
        (v, BOOLEAN) for v in chain.controller_events
    }
    program = Program(
        name_str,
        set(chain.states),
        chain.initial_state,
        [
            (str(v), symbol_table[str(v)])
            for v in state_vars + curr_state_vars + chain_snapshot_state_vars
        ],
        list(chain.transitions),
        [(v, symbol_table[str(v)]) for v in inputs],
        sorted(formula_only_con_events, key=lambda e: str(e[0])),
        preprocess=False,
        emit_state_binary_map=False,
    )
    return program, formula_objectives


def _build_formula_only_explicit_choice_program(
    *,
    name_str,
    inputs,
    state_vars,
    curr_state_vars,
    symbol_table,
    new_con_props,
    equality_choice_map,
    restricted_var_to_preds,
    input_snapshot_updates,
    formula_objectives,
    optimisation_summary: dict,
):
    var_by_name = {str(v): v for v in state_vars}
    ordered_choice_vars = sorted(equality_choice_map.keys())
    restricted_var_names = set(ordered_choice_vars)
    raw_eval_transitions = []
    for rhs_choice_tuple in itertools.product(
        *[equality_choice_map[var_name] for var_name in ordered_choice_vars]
    ):
        actions = [
            Update(var_by_name[var_name], rhs_choice_tuple[i])
            for i, var_name in enumerate(ordered_choice_vars)
        ]
        actions.extend(
            Update(v, NonDeterministic())
            for v in state_vars
            if str(v) not in restricted_var_names
        )
        actions.extend(input_snapshot_updates)
        raw_eval_transitions.append(Transition("eval", true(), actions, [], "eval"))

    raw_transitions = {"eval": raw_eval_transitions}
    det_symbol_table = dict(symbol_table)
    for v in new_con_props:
        det_symbol_table.setdefault(str(v), BOOLEAN)
    lose_transitions = _complete_raw_transitions_with_lose(
        raw_transitions, det_symbol_table
    )
    det_transitions, det_con_vars = determinise(
        raw_transitions,
        "formula",
        det_symbol_table,
    )
    all_transitions = det_transitions + lose_transitions
    symbol_table.update(det_symbol_table)
    symbol_table.update({str(v): BOOLEAN for v in det_con_vars})
    guard_replacement = _build_formula_update_predicate_guard_replacement(
        all_transitions,
        restricted_var_to_preds,
        symbol_table,
    )
    if len(guard_replacement) > 0:
        formula_objectives = [
            f.replace_formulas(guard_replacement) for f in formula_objectives
        ]
    _record_optimisation(
        optimisation_summary,
        "formula_only",
        "spot_update_predicates_rewritten_to_guards",
        len({str(k) for k in guard_replacement.keys() if not isinstance(k, MathExpr)}),
    )

    formula_only_con_events = {(v, BOOLEAN) for v in new_con_props} | {
        (v, BOOLEAN) for v in det_con_vars
    }
    program = Program(
        name_str,
        {"eval"} if len(lose_transitions) == 0 else {"eval", "lose"},
        "eval",
        [(str(v), symbol_table[str(v)]) for v in state_vars + curr_state_vars],
        all_transitions,
        [(v, symbol_table[str(v)]) for v in inputs],
        sorted(formula_only_con_events, key=lambda e: str(e[0])),
        preprocess=False,
        emit_state_binary_map=False,
    )
    return program, formula_objectives


def _build_formula_only_fallback_program(
    *,
    name_str,
    inputs,
    state_vars,
    curr_state_vars,
    symbol_table,
    formula_objectives,
    new_con_props,
    input_snapshot_updates,
    restricted_guard_by_var,
    active_spot_restriction_result,
    spot_restriction_result,
    optimisation_summary: dict,
    precomputed_guarantee_extraction_result=None,
    allow_guarantee_transition_extraction: bool,
):
    guarantee_extraction_result, formula_objectives = (
        _apply_formula_only_guarantee_extraction(
            formula_objectives=formula_objectives,
            state_vars=state_vars,
            symbol_table=symbol_table,
            new_con_props=new_con_props,
            optimisation_summary=optimisation_summary,
            precomputed_guarantee_extraction_result=precomputed_guarantee_extraction_result,
            allow_guarantee_transition_extraction=allow_guarantee_transition_extraction,
        )
    )

    eval_transition = Transition(
        "eval",
        true(),
        [Update(v, NonDeterministic()) for v in state_vars] + input_snapshot_updates,
        [],
        "eval",
    )
    if len(spot_restriction_result.restricted_var_to_guard) > 0:
        eval_transition.set_predicate_upgrades(
            [
                restricted_guard_by_var[var_name]
                for var_name in sorted(restricted_guard_by_var.keys())
            ]
        )

    if guarantee_extraction_result is not None and guarantee_extraction_result.applied:
        extracted_transitions = []
        for extracted in guarantee_extraction_result.transitions:
            updated_vars = {u.left for u in extracted.action}
            actions = list(extracted.action) + [
                Update(v, NonDeterministic())
                for v in state_vars
                if v not in updated_vars
            ]
            actions.extend(input_snapshot_updates)
            t = Transition(
                "eval",
                extracted.condition,
                actions,
                [],
                "eval",
            )
            if len(spot_restriction_result.restricted_var_to_guard) > 0:
                t.set_predicate_upgrades(
                    [
                        restricted_guard_by_var[var_name]
                        for var_name in sorted(restricted_guard_by_var.keys())
                    ]
                )
            extracted_transitions.append(t)
        (
            extracted_transitions,
            qe_update_overlap_merges,
        ) = _merge_extracted_transitions_with_qe_equivalent_overlaps(
            extracted_transitions,
            symbol_table,
        )
        _record_optimisation(
            optimisation_summary,
            "formula_only",
            "guarantee_transition_qe_equivalent_update_overlap_merges",
            qe_update_overlap_merges,
        )

        covered_guards = [t.condition for t in extracted_transitions]
        if len(covered_guards) > 0:
            fallback_guard = neg(disjunct_formula_set(covered_guards))
            fallback_guard = simplify_formula_with_math(fallback_guard, symbol_table)
            if sat(fallback_guard, symbol_table):
                reachability_goals = [
                    goal
                    for _, goal in sorted(
                        {
                            str(goal): goal
                            for goal in active_spot_restriction_result.restricted_var_to_goal.values()
                        }.items(),
                        key=lambda item: item[0],
                    )
                ]
                noncovered_is_winning_reachability = False
                if len(reachability_goals) > 0:
                    goals_disj = disjunct_formula_set(reachability_goals)
                    noncovered_is_winning_reachability = not sat(
                        conjunct(fallback_guard, neg(goals_disj)),
                        symbol_table,
                    )

                if noncovered_is_winning_reachability:
                    stutter_transition = Transition(
                        "eval",
                        fallback_guard,
                        [Update(v, v) for v in state_vars] + input_snapshot_updates,
                        [],
                        "eval",
                    )
                    if len(spot_restriction_result.restricted_var_to_guard) > 0:
                        stutter_transition.set_predicate_upgrades(
                            [
                                restricted_guard_by_var[var_name]
                                for var_name in sorted(restricted_guard_by_var.keys())
                            ]
                        )
                    extracted_transitions.append(stutter_transition)
                else:
                    # Leave uncovered region without an explicit fallback.
                    # Post formula-only determinisation will route it to `lose`,
                    # avoiding unnecessary minigame introduction on violating cases.
                    pass
        program_transitions = extracted_transitions
    else:
        program_transitions = [eval_transition]

    program = Program(
        name_str,
        {"eval"},
        "eval",
        [(str(v), symbol_table[str(v)]) for v in state_vars + curr_state_vars],
        program_transitions,
        [(v, symbol_table[str(v)]) for v in inputs],
        [(v, BOOLEAN) for v in new_con_props],
        preprocess=False,
        emit_state_binary_map=False,
    )
    return program, formula_objectives
