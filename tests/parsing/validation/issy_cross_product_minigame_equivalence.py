import argparse
import copy
import re
from dataclasses import dataclass
from pathlib import Path

import parsec

from analysis.compatibility_checking.program_to_nuxmv import program_to_nuxmv_model
from parsing.string_to_issy import (
    parser as issy_parser,
    _build_intermediate_game_program_data,
    _prepare_context,
    _cross_product_intermediate_programs,
)
from parsing.util.game_transition_utils import _resolve_nondeterminism
from .formula_update_booleanisation import extract_formula_updates
from .issy_translation_equivalence import (
    _dump_model_to_log,
    _ltl_check_with_trace,
    _model_var_names,
    _nu_model_to_module,
    _module_name,
    _sanitize_nuxmv_text,
)
from programs.program import fill_in_minigames
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.util import conjunct_formula_set
from prop_lang.variable import Variable


@dataclass
class CrossProductMinigameEquivalenceResult:
    compatible_holds: bool
    check_output: str
    bad_exit_eventually_holds: bool | None = None
    bad_exit_check_output: str | None = None
    model: str | None = None
    model_log_path: str | None = None
    counterexample_trace: str | None = None
    bad_exit_counterexample_trace: str | None = None


def _parse_issy_raw(input_text: str):
    input_wo_comments = re.sub("//.*(\n|$)", "", input_text).strip()
    return (issy_parser << parsec.eof()).parse(input_wo_comments)


def _build_pre_post_cross_product_programs(
    issy_text: str,
    issy_name: str,
    resolve_nondeterminism: bool = True,
):
    vars_or_macros, formula_objectives, games = _parse_issy_raw(issy_text)
    if len(games) == 0:
        raise Exception(
            "Cross-product/minigame equivalence requires ISSY files with game blocks."
        )

    problem_context = _prepare_context(
        vars_or_macros=vars_or_macros,
        formula_objectives=formula_objectives,
        optimisation_summary={},
    )
    (
        sub_programs,
        states_to_exclude_minigame,
        con_vars,
        symbol_table,
        declared_state_vars,
        normalized_formula_objectives,
    ) = _build_intermediate_game_program_data(issy_name, games, problem_context)

    (
        pre_program,
        _game_objectives,
        to_exclude_from_minigame,
        _lose_var,
    ) = _cross_product_intermediate_programs(
        issy_name,
        sub_programs,
        states_to_exclude_minigame,
        con_vars,
        symbol_table,
        declared_state_vars,
    )

    if resolve_nondeterminism and not pre_program.deterministic:
        pre_program, _post_cross_lose_var, to_exclude_from_minigame = (
            _resolve_nondeterminism(
                pre_program,
                symbol_table,
                list(to_exclude_from_minigame),
            )
        )

    # Keep the same stage ordering as in parsing.string_to_issy.process before minigame fill.
    preds_to_replace_in_ltl, non_det_v, new_con_props = extract_formula_updates(
        pre_program,
        conjunct_formula_set(normalized_formula_objectives),
    )
    if len(non_det_v) > 0:
        new_transitions = []
        for t in pre_program.transitions:
            new_actions = list(t.action)
            for v in non_det_v:
                new_actions.append(BiOp(v.prev_rep(), "=", NonDeterministic()))
            new_t = Transition(t.src, t.condition, new_actions, t.outputs, t.tgt)
            new_transitions.append(new_t)
        pre_program.transitions = new_transitions

    if len(new_con_props) > 0:
        for v in new_con_props:
            pre_program.symbol_table[str(v)] = BOOLEAN
            if not any(ev == v and ty == BOOLEAN for ev, ty in pre_program.con_events):
                pre_program.con_events.append((v, BOOLEAN))
            if v not in pre_program.outputs:
                pre_program.outputs.append(v)
            if v not in pre_program.inp_out_puts:
                pre_program.inp_out_puts.append(v)
            if v not in pre_program.bool_in_out:
                pre_program.bool_in_out.append(v)

    pre_program_snapshot = copy.deepcopy(pre_program)
    post_program, _minigame_states = fill_in_minigames(
        pre_program_snapshot,
        normalized_formula_objectives,
        to_exclude_from_minigame,
    )
    return pre_program, post_program, to_exclude_from_minigame


def _state_mapping_constraints(
    pre_program,
    post_program,
    to_exclude_from_minigame,
):
    excluded = {str(s) for s in to_exclude_from_minigame}
    post_states = set(post_program.states)
    minigame_states = sorted([s for s in post_program.states if "_minigame_" in s])

    mapping = {}
    for s in sorted(pre_program.states):
        if s in excluded and "lose" in post_states:
            mapping[s] = "lose"
        elif s in post_states:
            mapping[s] = s
        else:
            raise ValueError(
                f"Could not map pre-minigame state '{s}' into post-minigame program states."
            )

    grouped = {}
    for left_state, right_state in mapping.items():
        grouped.setdefault(right_state, []).append(left_state)

    current_constraints = []
    next_constraints = []
    for right_state, left_states in sorted(grouped.items()):
        if len(left_states) == 1:
            lhs_curr = f"left.{left_states[0]}"
            lhs_next = f"next(left.{left_states[0]})"
        else:
            lhs_curr = "(" + " | ".join(f"left.{s}" for s in sorted(left_states)) + ")"
            lhs_next = (
                "(" + " | ".join(f"next(left.{s})" for s in sorted(left_states)) + ")"
            )
        current_constraints.append(f"(right.{right_state} <-> {lhs_curr})")
        next_constraints.append(f"(next(right.{right_state}) <-> {lhs_next})")

    mapped_right = set(grouped.keys())
    for right_state in sorted(post_states):
        if right_state in mapped_right:
            continue
        if right_state in minigame_states:
            continue
        current_constraints.append(f"!right.{right_state}")
        next_constraints.append(f"!next(right.{right_state})")

    return current_constraints, next_constraints, minigame_states


def build_cross_product_minigame_equivalence_model(
    pre_program,
    post_program,
    to_exclude_from_minigame,
    *,
    compatibility_on_shared_numeric_state_vars_only: bool = False,
    synchronised_controller_var_prefixes: tuple[str, ...] = (),
    stutter_left_while_right_in_minigame: bool = False,
) -> tuple[str, str, str | None, bool]:
    left_model = program_to_nuxmv_model(pre_program)
    right_model = program_to_nuxmv_model(post_program)

    left_module_name = _module_name(pre_program.name + "_pre_minigame")
    right_module_name = _module_name(post_program.name + "_post_minigame")

    model_text = _nu_model_to_module(left_model, left_module_name)
    model_text += "\n" + _nu_model_to_module(right_model, right_module_name)
    left_var_names = _model_var_names(left_model)
    right_var_names = _model_var_names(right_model)
    shared_model_vars = sorted(left_var_names.intersection(right_var_names))

    left_inputs = {str(v) for v, _ in pre_program.env_events}
    right_inputs = {str(v) for v, _ in post_program.env_events}
    shared_inputs = sorted(left_inputs.intersection(right_inputs))
    if (left_inputs or right_inputs) and len(shared_inputs) == 0:
        raise ValueError(
            "No shared inputs between pre-minigame and post-minigame programs."
        )

    shared_local_vars = sorted(
        [v for v in pre_program.local_vars_str if v in set(post_program.local_vars_str)]
    )

    left_con = {str(v) for v, _ in pre_program.con_events}
    right_con = {str(v) for v, _ in post_program.con_events}
    shared_con_events = sorted(left_con.intersection(right_con))

    # Align modeled history variables that can affect guards (e.g., *_prev, *_prev_prev).
    history_bases = sorted(
        set(shared_local_vars) | set(shared_inputs) | set(shared_con_events)
    )
    shared_history_vars = []
    for base in history_bases:
        for suffix in ["_prev", "_prev_prev"]:
            hv = f"{base}{suffix}"
            if hv in left_var_names and hv in right_var_names:
                shared_history_vars.append(hv)

    (
        current_state_constraints,
        next_state_constraints,
        minigame_states,
    ) = _state_mapping_constraints(
        pre_program,
        post_program,
        to_exclude_from_minigame,
    )
    right_in_minigame = (
        "FALSE"
        if len(minigame_states) == 0
        else "(" + " | ".join([f"right.{s}" for s in minigame_states]) + ")"
    )
    right_next_in_minigame = (
        "FALSE"
        if len(minigame_states) == 0
        else "(" + " | ".join([f"next(right.{s})" for s in minigame_states]) + ")"
    )

    if compatibility_on_shared_numeric_state_vars_only:
        # Keep only shared numeric local state vars and ignore helper/new vars.
        compat_state_vars = []
        for v in shared_local_vars:
            if v.startswith("int_") or v.startswith("curr_") or v.startswith("__nd_"):
                continue
            left_t = pre_program.symbol_table.get(v)
            right_t = post_program.symbol_table.get(v)
            if left_t == BOOLEAN or right_t == BOOLEAN:
                continue
            compat_state_vars.append(v)
        compat_vars = sorted(set(compat_state_vars))
    else:
        # Compatibility checks behavioural agreement on shared local state only.
        # Shared inputs/controller propositions are assumed equal separately.
        compat_vars = sorted(set(shared_local_vars))

    assumed_shared_vars = sorted(
        [
            v
            for v in (set(shared_inputs) | set(shared_con_events))
            if v in left_var_names and v in right_var_names
        ]
    )

    synchronised_controller_vars = []
    if len(synchronised_controller_var_prefixes) > 0:
        synchronised_controller_vars = sorted(
            [
                v
                for v in shared_model_vars
                if any(
                    v.startswith(prefix)
                    for prefix in synchronised_controller_var_prefixes
                )
            ]
        )
    current_var_match = [f"(left.{v} = right.{v})" for v in compat_vars]
    next_var_match = [f"(next(left.{v}) = next(right.{v}))" for v in compat_vars]
    current_var_match_formula = (
        "TRUE" if len(current_var_match) == 0 else " & ".join(current_var_match)
    )
    next_var_match_formula = (
        "TRUE" if len(next_var_match) == 0 else " & ".join(next_var_match)
    )
    current_state_match = (
        "TRUE"
        if len(current_state_constraints) == 0
        else " & ".join(current_state_constraints)
    )
    next_state_match = (
        "TRUE"
        if len(next_state_constraints) == 0
        else " & ".join(next_state_constraints)
    )
    right_has_lose = "lose" in set(post_program.states)
    if right_has_lose:
        # In states collapsed to `lose`, local valuations may intentionally diverge.
        # Keep state-mapping equality, but relax local-value equality under `right.lose`.
        current_match = (
            f"({current_state_match}) & ((right.lose) | ({current_var_match_formula}))"
        )
        next_match = (
            f"({next_state_match}) & ((next(right.lose)) | ({next_var_match_formula}))"
        )
    else:
        current_match = f"({current_state_match}) & ({current_var_match_formula})"
        next_match = f"({next_state_match}) & ({next_var_match_formula})"

    init_compatible = (
        f"(({right_in_minigame}) | (!( {right_in_minigame} ) & ({current_match})))"
    )
    next_compatible = f"(({right_next_in_minigame}) | (!( {right_next_in_minigame} ) & ({next_match})))"

    main_init = []
    if not compatibility_on_shared_numeric_state_vars_only:
        main_init.extend([f"left.{v} = right.{v}" for v in shared_history_vars])
    if current_match != "TRUE":
        main_init.append(current_match)
    main_init.extend([f"left.{v} = right.{v}" for v in synchronised_controller_vars])
    if stutter_left_while_right_in_minigame and "other_game_in_minigame" in left_var_names:
        main_init.append(f"(left.other_game_in_minigame = {right_in_minigame})")
    main_init.append(f"compatible = {init_compatible}")

    main_trans = []
    main_trans.extend(
        [f"next(left.{v}) = next(right.{v})" for v in synchronised_controller_vars]
    )
    if stutter_left_while_right_in_minigame and "other_game_in_minigame" in left_var_names:
        main_trans.append(f"(left.other_game_in_minigame = {right_in_minigame})")
        main_trans.append(
            f"(next(left.other_game_in_minigame) = {right_next_in_minigame})"
        )
    main_trans.append(f"next(compatible) = {next_compatible}")

    model_text += "MODULE main\n"
    model_text += (
        "VAR\n\tleft : "
        + left_module_name
        + ";\n\tright : "
        + right_module_name
        + ";\n\tcompatible : boolean;\n"
    )
    if len(assumed_shared_vars) > 0:
        model_text += (
            "INVAR\n\t("
            + ")\n\t& (".join(f"left.{v} = right.{v}" for v in assumed_shared_vars)
            + ")\n"
        )
    model_text += f"DEFINE\n\tin_minigame := {right_in_minigame};\n"
    if len(main_init) > 0:
        model_text += "INIT\n\t(" + ")\n\t& (".join(main_init) + ")\n"
    if len(main_trans) > 0:
        model_text += "TRANS\n\t(" + ")\n\t& (".join(main_trans) + ")\n"

    has_minigame = len(minigame_states) > 0
    compatibility_ltl = "G(compatible)"
    boundary_exit_ltl = "(in_minigame & X(!in_minigame))"
    if has_minigame:
        guarded_compatibility_ltl = (
            f"(G(({boundary_exit_ltl}) -> X(compatible)) -> {compatibility_ltl})"
        )
        # Existential bad-exit path check encoded via universal safety:
        # exists bad path iff G(!bad_exit) is false.
        bad_exit_eventually_ltl: str | None = (
            f"G(!(({boundary_exit_ltl}) & X(!compatible)))"
        )
    else:
        guarded_compatibility_ltl = compatibility_ltl
        bad_exit_eventually_ltl = None

    return (
        _sanitize_nuxmv_text(model_text),
        guarded_compatibility_ltl,
        bad_exit_eventually_ltl,
        has_minigame,
    )


def check_cross_product_minigame_equivalence_from_text(
    issy_text: str,
    issy_name: str = "issy_input",
    return_model: bool = False,
    log_dir: str | None = None,
) -> CrossProductMinigameEquivalenceResult:
    pre_program, post_program, to_exclude_from_minigame = (
        _build_pre_post_cross_product_programs(issy_text, issy_name)
    )
    (
        model_text,
        compatibility_ltl,
        bad_exit_eventually_ltl,
        _has_minigame,
    ) = build_cross_product_minigame_equivalence_model(
        pre_program,
        post_program,
        to_exclude_from_minigame,
        stutter_left_while_right_in_minigame=True,
    )
    model_log_path = _dump_model_to_log(
        model_text, issy_name + "_cross_product_minigame", log_dir=log_dir
    )

    compatible_ok, checker_out, counterexample_trace = _ltl_check_with_trace(
        model_text,
        compatibility_ltl,
        add_trace_when_result_is=False,
    )

    if bad_exit_eventually_ltl is not None:
        no_bad_exit_holds, bad_exit_out, bad_exit_trace = _ltl_check_with_trace(
            model_text,
            bad_exit_eventually_ltl,
            add_trace_when_result_is=False,
        )
        bad_exit_holds = not no_bad_exit_holds
    else:
        bad_exit_holds = None
        bad_exit_out = (
            "SKIPPED: no minigame states in post-minigame program; "
            "boundary-specific bad-exit check is not applicable."
        )
        bad_exit_trace = None

    return CrossProductMinigameEquivalenceResult(
        compatible_holds=compatible_ok,
        check_output=checker_out,
        bad_exit_eventually_holds=bad_exit_holds,
        bad_exit_check_output=bad_exit_out,
        model=model_text if return_model else None,
        model_log_path=model_log_path,
        counterexample_trace=counterexample_trace,
        bad_exit_counterexample_trace=bad_exit_trace,
    )


def check_cross_product_minigame_equivalence_from_file(
    issy_path: str,
    return_model: bool = False,
    log_dir: str | None = None,
) -> CrossProductMinigameEquivalenceResult:
    issy_file = Path(issy_path)
    return check_cross_product_minigame_equivalence_from_text(
        issy_file.read_text(),
        issy_name=issy_file.name,
        return_model=return_model,
        log_dir=log_dir,
    )


def _main():
    parser = argparse.ArgumentParser(
        description=(
            "Check equivalence between cross-product program semantics "
            "before and after minigame resolution."
        )
    )
    parser.add_argument("--issy", required=True, help="Path to .issy file")
    parser.add_argument(
        "--dump-model",
        default=None,
        help="Optional path where the combined nuXmv model should be written",
    )
    parser.add_argument(
        "--model-log-dir",
        default=None,
        help=(
            "Directory where the combined model used during verification is logged. "
            "Default: src/logs/issy_translation_equivalence"
        ),
    )
    args = parser.parse_args()

    result = check_cross_product_minigame_equivalence_from_file(
        args.issy,
        return_model=args.dump_model is not None,
        log_dir=args.model_log_dir,
    )
    print("compatible_holds:", result.compatible_holds)
    print("bad_exit_eventually_holds:", result.bad_exit_eventually_holds)
    if result.bad_exit_check_output is not None:
        print("bad_exit_check_output:", result.bad_exit_check_output)
    if result.model_log_path is not None:
        print("model_logged_to:", result.model_log_path)
    if result.counterexample_trace is not None:
        print("counterexample_trace:")
        print(result.counterexample_trace)
    if result.bad_exit_counterexample_trace is not None:
        print("bad_exit_counterexample_trace:")
        print(result.bad_exit_counterexample_trace)

    if args.dump_model is not None and result.model is not None:
        Path(args.dump_model).write_text(result.model)
        print("combined_model_written_to:", args.dump_model)

    if (not result.compatible_holds) or (result.bad_exit_eventually_holds is True):
        raise SystemExit(1)


if __name__ == "__main__":
    _main()
