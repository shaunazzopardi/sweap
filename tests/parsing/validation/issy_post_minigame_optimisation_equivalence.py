import argparse
import copy
import re
from dataclasses import dataclass
from pathlib import Path

import parsec

from parsing.string_to_issy import (
    parser as issy_parser,
    _build_intermediate_game_program_data,
    _prepare_context,
    _cross_product_intermediate_programs,
    _resolve_nondeterminism_after_cross_product,
    _postprocess_booleanise_strict_updates_on_final_program,
)
from .formula_update_booleanisation import extract_formula_updates
from .issy_cross_product_minigame_equivalence import (
    build_cross_product_minigame_equivalence_model,
)
from .issy_translation_equivalence import (
    _dump_model_to_log,
    _ltl_check_with_trace,
)
from programs.program import fill_in_minigames
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN
from prop_lang.util import conjunct_formula_set


@dataclass
class PostMinigameOptimisationEquivalenceResult:
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


def _build_minigame_baseline_and_optimised_programs(
    issy_text: str,
    issy_name: str,
    resolve_nondeterminism: bool = True,
):
    vars_or_macros, formula_objectives, games = _parse_issy_raw(issy_text)
    if len(games) == 0:
        raise Exception(
            "Post-minigame optimisation equivalence requires ISSY files with game blocks."
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
        program,
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

    if resolve_nondeterminism and not program.deterministic:
        program, _post_cross_lose_var, to_exclude_from_minigame = (
            _resolve_nondeterminism_after_cross_product(
                program,
                symbol_table,
                list(to_exclude_from_minigame),
            )
        )

    # Keep the same preparation steps as in parsing.string_to_issy.process stage 4.
    _preds_to_replace_in_ltl, non_det_v, new_con_props = extract_formula_updates(
        program,
        conjunct_formula_set(normalized_formula_objectives),
    )
    if len(non_det_v) > 0:
        new_transitions = []
        for t in program.transitions:
            new_actions = list(t.action)
            for v in non_det_v:
                new_actions.append(BiOp(v.prev_rep(), "=", NonDeterministic()))
            new_t = Transition(t.src, t.condition, new_actions, t.outputs, t.tgt)
            new_transitions.append(new_t)
        program.transitions = new_transitions

    if len(new_con_props) > 0:
        for v in new_con_props:
            program.symbol_table[str(v)] = BOOLEAN
            if not any(ev == v and ty == BOOLEAN for ev, ty in program.con_events):
                program.con_events.append((v, BOOLEAN))
            if v not in program.outputs:
                program.outputs.append(v)
            if v not in program.inp_out_puts:
                program.inp_out_puts.append(v)
            if v not in program.bool_in_out:
                program.bool_in_out.append(v)

    # Baseline after minigame resolution.
    baseline_program, _minigame_states = fill_in_minigames(
        copy.deepcopy(program),
        normalized_formula_objectives,
        to_exclude_from_minigame,
    )

    # Optimised version after post-minigame strict-update booleanisation.
    optimised_program = copy.deepcopy(baseline_program)
    _postprocess_booleanise_strict_updates_on_final_program(
        optimised_program,
        list(normalized_formula_objectives),
    )

    return baseline_program, optimised_program


def check_post_minigame_optimisation_equivalence_from_text(
    issy_text: str,
    issy_name: str = "issy_input",
    return_model: bool = False,
    log_dir: str | None = None,
) -> PostMinigameOptimisationEquivalenceResult:
    baseline_program, optimised_program = (
        _build_minigame_baseline_and_optimised_programs(issy_text, issy_name)
    )

    # Reuse the same compatibility/minigame-boundary guarantees as the existing checker.
    model_text, compatibility_ltl, bad_exit_eventually_ltl, _has_minigame = (
        build_cross_product_minigame_equivalence_model(
            baseline_program,
            optimised_program,
            [],
            # For post-minigame optimisation we require full behavioural alignment
            # under the same inputs/controller propositions, not just numeric locals.
            compatibility_on_shared_numeric_state_vars_only=False,
            synchronised_controller_var_prefixes=(
                "eq_",
                "sat_",
                "game_con_",
                "minigame_event_",
            ),
        )
    )
    model_log_path = _dump_model_to_log(
        model_text,
        issy_name + "_post_minigame_optimisation",
        log_dir=log_dir,
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
            "SKIPPED: no minigame states in compared models; "
            "boundary-specific bad-exit check is not applicable."
        )
        bad_exit_trace = None

    return PostMinigameOptimisationEquivalenceResult(
        compatible_holds=compatible_ok,
        check_output=checker_out,
        bad_exit_eventually_holds=bad_exit_holds,
        bad_exit_check_output=bad_exit_out,
        model=model_text if return_model else None,
        model_log_path=model_log_path,
        counterexample_trace=counterexample_trace,
        bad_exit_counterexample_trace=bad_exit_trace,
    )


def check_post_minigame_optimisation_equivalence_from_file(
    issy_path: str,
    return_model: bool = False,
    log_dir: str | None = None,
) -> PostMinigameOptimisationEquivalenceResult:
    issy_file = Path(issy_path)
    return check_post_minigame_optimisation_equivalence_from_text(
        issy_file.read_text(),
        issy_name=issy_file.name,
        return_model=return_model,
        log_dir=log_dir,
    )


def _main():
    parser = argparse.ArgumentParser(
        description=(
            "Check equivalence between minigame-resolved baseline and "
            "the post-minigame optimised program."
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

    result = check_post_minigame_optimisation_equivalence_from_file(
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
