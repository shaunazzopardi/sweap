import argparse
import re
from dataclasses import dataclass
from pathlib import Path
import time
import subprocess
from tempfile import NamedTemporaryFile

import parsec

from analysis.compatibility_checking.program_to_nuxmv import program_to_nuxmv_model
from analysis.compatibility_checking.renderer import render_structured_model
from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl
from analysis.model_checker import ModelChecker, nuxmv_path
from parsing.string_to_issy import (
    parser as issy_parser,
    string_to_issy,
    _build_process_context,
)
from parsing.string_to_program import string_to_program
from parsing.string_to_rpg import parity_objective
from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.types.types import BOOLEAN
from prop_lang.util import (
    F,
    G,
    conjunct_formula_set,
    disjunct_formula_set,
    true,
)
from prop_lang.variable import Variable


@dataclass
class BareIssySpec:
    name: str
    inputs: list[Variable]
    state_vars: list[Variable]
    symbol_table: dict[str, object]
    loc_var_names: list[str]
    objective: Formula
    model: StructuredNuXmvModel


@dataclass
class IssyTranslationEquivalenceResult:
    compatible_holds: bool
    check_output: str
    bad_exit_eventually_holds: bool | None = None
    bad_exit_check_output: str | None = None
    model: str | None = None
    model_log_path: str | None = None
    counterexample_trace: str | None = None
    bad_exit_counterexample_trace: str | None = None


def _sanitize_nuxmv_text(text: str) -> str:
    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text


def _module_name(base: str) -> str:
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", base).upper()
    if not sanitized:
        sanitized = "MODEL"
    if sanitized[0].isdigit():
        sanitized = "M_" + sanitized
    return sanitized


def _dump_model_to_log(
    model_text: str, issy_name: str, log_dir: str | None = None
) -> str:
    if log_dir is None:
        out_dir = (
            Path(__file__).resolve().parents[2]
            / "logs"
            / "issy_translation_equivalence"
        )
    else:
        out_dir = Path(log_dir)
    try:
        out_dir.mkdir(parents=True, exist_ok=True)
    except PermissionError:
        out_dir = Path("/tmp/issy_translation_equivalence")
        out_dir.mkdir(parents=True, exist_ok=True)
    stem = _module_name(issy_name).lower()
    file_path = out_dir / f"{stem}_{int(time.time() * 1000)}.smv"
    file_path.write_text(model_text)
    return str(file_path)


def _emit_section(name: str, entries: list[str]) -> str:
    if not entries:
        return ""
    return f"{name}\n\t" + ";\n\t".join(entries) + ";\n"


def _extract_counterexample_trace(nuxmv_output: str) -> str | None:
    marker = "Trace Description:"
    idx = nuxmv_output.find(marker)
    if idx == -1:
        return None
    return nuxmv_output[idx:].strip()


def _run_nuxmv_trace_check(model_text: str, ltl_property: str) -> str:
    with (
        NamedTemporaryFile("w", suffix=".smv", delete=False) as model,
        NamedTemporaryFile("w", suffix=".txt", delete=False) as commands,
    ):
        model.write(model_text)
        model.close()
        commands.write("go\n")
        commands.write(f'check_ltlspec -p "{ltl_property}"\n')
        commands.write("show_traces -v\n")
        commands.write("quit\n")
        commands.close()
        try:
            return subprocess.check_output(
                [nuxmv_path, "-source", commands.name, model.name],
                encoding="utf-8",
                stderr=subprocess.STDOUT,
            )
        finally:
            Path(model.name).unlink(missing_ok=True)
            Path(commands.name).unlink(missing_ok=True)


def _ltl_check_with_trace(
    model_text: str,
    ltl_property: str,
    add_trace_when_result_is: bool | None = None,
) -> tuple[bool, str, str | None]:
    checker = ModelChecker()
    holds, checker_out = checker.invar_check(model_text, ltl_property, None, True)
    if holds not in (True, False):
        raise RuntimeError(
            "nuXmv returned an unexpected result while checking LTL property."
        )

    trace = _extract_counterexample_trace(checker_out)
    should_add_trace = (add_trace_when_result_is is None) or (
        holds == add_trace_when_result_is
    )
    if trace is None and should_add_trace:
        trace_out = _run_nuxmv_trace_check(model_text, ltl_property)
        trace = _extract_counterexample_trace(trace_out)
    return holds, checker_out, trace


def _nu_model_to_module(model: StructuredNuXmvModel, module_name: str) -> str:
    module_model = StructuredNuXmvModel(
        name=module_name,
        vars=list(model.vars),
        define=list(model.define),
        init=list(model.init),
        invar=list(model.invar),
        trans=list(model.trans),
    )
    return _sanitize_nuxmv_text(render_structured_model(module_model))


def _prefix_vars(expr: str, var_names: set[str], instance: str) -> str:
    out = expr
    for name in sorted(var_names, key=len, reverse=True):
        pattern = rf"(?<![A-Za-z0-9_@$-]){re.escape(name)}(?![A-Za-z0-9_@$-])"
        out = re.sub(pattern, f"{instance}.{name}", out)
    return out


def _model_var_names(model: StructuredNuXmvModel) -> set[str]:
    return {v.name for v in model.vars}


def _one_hot_invars(vars_here: list[str]) -> list[str]:
    if len(vars_here) == 0:
        return []
    invars = ["(" + " | ".join(vars_here) + ")"]
    for i in range(len(vars_here)):
        for j in range(i + 1, len(vars_here)):
            invars.append(f"!({vars_here[i]} & {vars_here[j]})")
    return invars


def _parse_issy_raw(input_text: str):
    input_wo_comments = re.sub("//.*(\n|$)", "", input_text).strip()
    return (issy_parser << parsec.eof()).parse(input_wo_comments)


def build_bare_issy_spec(issy_text: str, issy_name: str = "issy_input") -> BareIssySpec:
    vars_or_macros, formula_objectives, games = _parse_issy_raw(issy_text)
    (
        inputs,
        state_vars,
        macros,
        formula_objectives,
        symbol_table,
    ) = _build_process_context(vars_or_macros, formula_objectives)

    games = [
        (
            game_type,
            init,
            locs,
            [(src, f.replace_formulas(macros), tgt) for src, f, tgt in transitions],
        )
        for game_type, init, locs, transitions in games
    ]
    if len(games) == 0:
        raise Exception(
            "ISSY translation equivalence validator currently supports only ISSY files with game blocks."
        )

    vars_decl = []
    vars_decl.extend(
        [
            f"{v.name} : {'boolean' if symbol_table[v.name] == BOOLEAN else 'integer'}"
            for v in inputs
        ]
    )
    vars_decl.extend(
        [
            f"{v.name} : {'boolean' if symbol_table[v.name] == BOOLEAN else 'integer'}"
            for v in state_vars
        ]
    )

    init = []
    invar = []
    trans = []
    loc_var_names = []
    game_objectives = []

    for game_index, (
        game_type,
        init_loc,
        locs_in_game,
        transitions_in_game,
    ) in enumerate(games):
        locs = [str(v) for v, _, _ in locs_in_game]
        loc_var_map = {
            loc: f"issy_g{game_index}_loc_{loc}" for loc in sorted(set(locs))
        }
        loc_vars = [loc_var_map[loc] for loc in sorted(set(locs))]
        loc_var_names.extend(loc_vars)
        vars_decl.extend([f"{v} : boolean" for v in loc_vars])

        init.append(loc_var_map[init_loc])
        init.extend([f"!{v}" for loc, v in loc_var_map.items() if loc != init_loc])
        invar.extend(_one_hot_invars(loc_vars))

        src_to_trans = {loc: [] for loc in loc_var_map.keys()}
        for src, formula, tgt in transitions_in_game:
            src_var = loc_var_map[src]
            tgt_var = loc_var_map[tgt]
            tgt_assign = [f"next({tgt_var})"] + [
                f"!next({v})" for v in loc_vars if v != tgt_var
            ]
            clause = (
                "("
                + src_var
                + " & ("
                + formula.to_nuxmv()
                + ") & ("
                + " & ".join(tgt_assign)
                + "))"
            )
            src_to_trans[src].append(clause)

        for src, clauses in src_to_trans.items():
            src_var = loc_var_map[src]
            if len(clauses) == 0:
                trans.append(f"!{src_var}")
            else:
                trans.append(f"({src_var} -> ({' | '.join(clauses)}))")

        marked_states = {}
        for loc, _, mark in locs_in_game:
            marked_states.setdefault(mark, []).append(Variable(loc_var_map[str(loc)]))

        match game_type:
            case "Safety":
                marked = marked_states.get(1, [])
                if len(marked) == len(locs_in_game):
                    game_objectives.append(true())
                else:
                    game_objectives.append(G(disjunct_formula_set(marked)))
            case "Reachability":
                game_objectives.append(
                    F(disjunct_formula_set(marked_states.get(1, [])))
                )
            case "Buechi":
                game_objectives.append(
                    G(F(disjunct_formula_set(marked_states.get(1, []))))
                )
            case "ParityMaxOdd":
                game_objectives.append(parity_objective(marked_states))
            case _:
                raise Exception("Unknown game type: " + str(game_type))

    if len(games) == 0:
        trans.append("TRUE")

    # Ignore formula blocks by design for this validator; focus on game semantics.
    objective = conjunct_formula_set(game_objectives)
    vars_typed = []
    for decl in vars_decl:
        if ":" not in decl:
            raise ValueError(f"Invalid nuXmv var declaration: {decl}")
        name, typ = decl.split(":", 1)
        vars_typed.append(VarDecl(name.strip(), typ.strip()))
    model = StructuredNuXmvModel(
        name=issy_name + "_bare",
        vars=vars_typed,
        define=[],
        init=init,
        invar=invar,
        trans=trans,
    )
    return BareIssySpec(
        name=issy_name,
        inputs=inputs,
        state_vars=state_vars,
        symbol_table=symbol_table,
        loc_var_names=sorted(set(loc_var_names)),
        objective=objective,
        model=model,
    )


def build_issy_translation_equivalence_model(
    bare_spec: BareIssySpec,
    generated_program: Program,
    generated_objective: Formula,
) -> tuple[str, str, str, str | None, bool]:
    if generated_objective is None:
        raise ValueError("Generated program has no objective.")

    left_model = bare_spec.model
    right_model = program_to_nuxmv_model(generated_program)

    left_module_name = _module_name(bare_spec.name + "_bare_issy")
    right_module_name = _module_name(generated_program.name + "_generated_prog")

    model_text = _nu_model_to_module(left_model, left_module_name)
    model_text += "\n" + _nu_model_to_module(right_model, right_module_name)

    left_var_names = _model_var_names(left_model)
    right_var_names = _model_var_names(right_model)

    left_inputs = {v.name for v in bare_spec.inputs}
    right_inputs = {str(v) for v, _ in generated_program.env_events}
    shared_inputs = sorted(left_inputs.intersection(right_inputs))
    if (left_inputs or right_inputs) and len(shared_inputs) == 0:
        raise ValueError(
            "No shared environment inputs between bare ISSY model and generated program model."
        )

    generated_state_vars = set(generated_program.local_vars_str)
    state_var_mapping = {}
    for issy_v in bare_spec.state_vars:
        name = issy_v.name
        if name in generated_state_vars:
            state_var_mapping[name] = name
        elif ("int_" + name) in generated_state_vars:
            state_var_mapping[name] = "int_" + name
        elif ("curr_" + name) in generated_state_vars:
            state_var_mapping[name] = "curr_" + name
    if len(state_var_mapping) == 0:
        raise ValueError(
            "No shared state variables between bare ISSY model and generated program model."
        )

    right_minigame_states = sorted(
        [s for s in generated_program.states if "_minigame_" in s]
    )
    has_minigame = len(right_minigame_states) > 0
    right_in_minigame = (
        "FALSE"
        if len(right_minigame_states) == 0
        else "(" + " | ".join([f"right.{s}" for s in right_minigame_states]) + ")"
    )
    main_init = [f"left.{v} = right.{v}" for v in shared_inputs]
    # Assume both models start from the same valuation on shared state vars.
    main_init.extend(
        [f"left.{lv} = right.{rv}" for lv, rv in sorted(state_var_mapping.items())]
    )
    main_trans = [f"next(left.{v}) = next(right.{v})" for v in shared_inputs]

    current_state_match = " & ".join(
        [f"left.{lv} = right.{rv}" for lv, rv in sorted(state_var_mapping.items())]
    )
    next_state_match = " & ".join(
        [
            f"next(left.{lv}) = next(right.{rv})"
            for lv, rv in sorted(state_var_mapping.items())
        ]
    )
    right_next_in_minigame = (
        "FALSE"
        if len(right_minigame_states) == 0
        else "(" + " | ".join([f"next(right.{s})" for s in right_minigame_states]) + ")"
    )
    right_curr_in_minigame = right_in_minigame

    init_compatible = f"(({right_curr_in_minigame}) | (!( {right_curr_in_minigame} ) & ({current_state_match})))"
    next_compatible = f"(({right_next_in_minigame}) | (!( {right_next_in_minigame} ) & ({next_state_match})))"
    main_init.append(f"compatible = {init_compatible}")
    main_trans.append(f"next(compatible) = {next_compatible}")
    left_obj = _prefix_vars(
        _sanitize_nuxmv_text(bare_spec.objective.to_nuxmv()),
        left_var_names,
        "left",
    )
    right_obj = _prefix_vars(
        _sanitize_nuxmv_text(generated_objective.to_nuxmv()),
        right_var_names,
        "right",
    )
    objective_equivalence_ltl = f"(({left_obj}) <-> ({right_obj}))"

    model_text += "MODULE main\n"
    model_text += (
        "VAR\n\tleft : "
        + left_module_name
        + ";\n\tright : "
        + right_module_name
        + ";\n\tcompatible : boolean;\n"
    )
    model_text += f"DEFINE\n\tin_minigame := {right_curr_in_minigame};\n"
    if len(main_init) > 0:
        model_text += "INIT\n\t(" + ")\n\t& (".join(main_init) + ")\n"
    if len(main_trans) > 0:
        model_text += "TRANS\n\t(" + ")\n\t& (".join(main_trans) + ")\n"

    # The primary property checked by this validator.
    compatibility_ltl = "G(compatible)"
    boundary_exit_ltl = "(in_minigame & X(!in_minigame))"
    if has_minigame:
        boundary_implies_compatibility_ltl = (
            f"(G(({boundary_exit_ltl}) -> X(compatible)) -> {compatibility_ltl})"
        )
        bad_exit_eventually_ltl: str | None = (
            f"F(({boundary_exit_ltl}) & X(!compatible))"
        )
    else:
        # No minigame boundary exists; check direct compatibility only.
        boundary_implies_compatibility_ltl = compatibility_ltl
        bad_exit_eventually_ltl = None
    return (
        _sanitize_nuxmv_text(model_text),
        boundary_implies_compatibility_ltl,
        objective_equivalence_ltl,
        bad_exit_eventually_ltl,
        has_minigame,
    )


def check_issy_translation_equivalence_from_text(
    issy_text: str,
    issy_name: str = "issy_input",
    prog_text: str | None = None,
    return_model: bool = False,
    log_dir: str | None = None,
) -> IssyTranslationEquivalenceResult:
    bare_spec = build_bare_issy_spec(issy_text, issy_name)
    if prog_text is None:
        generated_program, generated_objective = string_to_issy(issy_text, issy_name)
    else:
        generated_program, generated_objective = string_to_program(prog_text)

    model_text, compatibility_ltl, _, bad_exit_eventually_ltl, _has_minigame = (
        build_issy_translation_equivalence_model(
            bare_spec, generated_program, generated_objective
        )
    )
    model_log_path = _dump_model_to_log(model_text, issy_name, log_dir=log_dir)

    compatible_ok, checker_out, counterexample_trace = _ltl_check_with_trace(
        model_text,
        compatibility_ltl,
        add_trace_when_result_is=False,
    )
    if bad_exit_eventually_ltl is not None:
        bad_exit_holds, bad_exit_out, bad_exit_trace = _ltl_check_with_trace(
            model_text,
            bad_exit_eventually_ltl,
            add_trace_when_result_is=True,
        )
    else:
        bad_exit_holds = None
        bad_exit_out = (
            "SKIPPED: no minigame states in generated model; "
            "boundary-specific bad-exit check is not applicable."
        )
        bad_exit_trace = None

    return IssyTranslationEquivalenceResult(
        compatible_holds=compatible_ok,
        check_output=checker_out,
        bad_exit_eventually_holds=bad_exit_holds,
        bad_exit_check_output=bad_exit_out,
        model=model_text if return_model else None,
        model_log_path=model_log_path,
        counterexample_trace=counterexample_trace,
        bad_exit_counterexample_trace=bad_exit_trace,
    )


def check_issy_translation_equivalence_from_files(
    issy_path: str,
    prog_path: str | None = None,
    return_model: bool = False,
    log_dir: str | None = None,
) -> IssyTranslationEquivalenceResult:
    issy_file = Path(issy_path)
    prog_text = None if prog_path is None else Path(prog_path).read_text()
    return check_issy_translation_equivalence_from_text(
        issy_file.read_text(),
        issy_name=issy_file.name,
        prog_text=prog_text,
        return_model=return_model,
        log_dir=log_dir,
    )


def _main():
    parser = argparse.ArgumentParser(
        description=(
            "Build a bare ISSY nuXmv model (before Program generation) and check "
            "equivalence against generated/loaded .prog semantics."
        )
    )
    parser.add_argument("--issy", required=True, help="Path to .issy file")
    parser.add_argument(
        "--prog",
        default=None,
        help="Optional .prog file path. If omitted, uses Program generated from ISSY.",
    )
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

    result = check_issy_translation_equivalence_from_files(
        args.issy,
        prog_path=args.prog,
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
