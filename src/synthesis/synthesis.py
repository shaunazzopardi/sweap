import logging
import os
import resource
import time
import analysis.abstraction.effects_abstraction.effects_to_ltl as effects_to_ltl
import config

from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.abstraction.interface.ltl_abstraction_type import (
    LTLAbstractionStructureType,
    LTLAbstractionTransitionType,
    LTLAbstractionBaseType,
    LTLAbstractionType,
    LTLAbstractionOutputType,
)
from analysis.compatibility_checking.strategy_verification import verify_strategy
from analysis.refinement.refinement import refinement_standard
from parsing.string_to_ltl import string_to_ltl_with_predicates
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import BoolBiOps
from prop_lang.types.types import BOOLEAN
from prop_lang.types.values import BoolAtoms
from prop_lang.util import (
    true,
    atomic_predicates,
    finite_state_preds,
    strip_mathexpr,
    normalise_pred_multiple_vars,
    conjunct_formula_set,
    implies,
    massage_ltl_for_dual,
    neg,
    is_tautology,
    is_contradictory,
    false,
    sat,
)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.ltl import ltl_synthesis
from synthesis.ltl.syfco_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem
from pathlib import Path

from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine
from synthesis.machines.wrapped_hoa import WrappedHOA
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from typing import List, Tuple


def synthesize(
    program: Program,
    ltl: Formula | None,
    tlsf_path: str | None,
    bound: int = -1,
) -> WrappedHOA:
    if config.Config.getConfig().debug and not program.deterministic:
        raise Exception(
            "Program is non-deterministic; synthesis may fail. Please ensure the program is deterministic, e.g. by adding appropriate assumptions or resolving non-determinism in the program."
        )

    start = time.time()
    (
        ltl_assumptions,
        ltl_guarantees,
        in_acts,
        out_acts,
    ) = process_specifications(program, ltl, tlsf_path)

    aps = set()
    for ass_or_guar in (ltl_assumptions, ltl_guarantees):
        for x in ass_or_guar:
            aps.update(atomic_predicates(x))

    wrapped_hoa: WrappedHOA = abstract_synthesis_loop(
        program,
        ltl_assumptions,
        ltl_guarantees,
        ltl,
        in_acts,
        out_acts,
        bound,
    )
    logging.info("synthesis took " + str(time.time() - start))
    return wrapped_hoa


def process_specifications(
    program: Program, ltl: Formula | None, tlsf_path: str | None
) -> Tuple[
    List[Formula],
    List[Formula],
    List[Variable],
    List[Variable],
]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if ' Error"' in ltl_text:
            raise Exception(
                "Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text
            )
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)

        ltl = string_to_ltl_with_predicates(ltl_text)
    elif ltl:
        in_acts_syfco = []
        out_acts_syfco = []
    else:
        raise Exception("No LTL specification provided.")

    if isinstance(ltl, BiOp) and ltl.op == BoolBiOps.IMPL:
        ltl_assumptions_formula = ltl.left
        ltl_guarantees_formula = ltl.right
    else:
        ltl_assumptions_formula = true()
        ltl_guarantees_formula: Formula = ltl

    if (
        isinstance(ltl_assumptions_formula, BiOp)
        and ltl_assumptions_formula.op == BoolBiOps.CONJ
    ):
        ltl_assumptions = ltl_assumptions_formula.sub_formulas_up_to_associativity()
    else:
        ltl_assumptions = [ltl_assumptions_formula]

    ltl_guarantees: list[Formula]
    if (
        isinstance(ltl_guarantees_formula, BiOp)
        and ltl_guarantees_formula.op == BoolBiOps.CONJ
    ):
        ltl_guarantees = ltl_guarantees_formula.sub_formulas_up_to_associativity()
    else:
        ltl_guarantees = [ltl_guarantees_formula]

    if config.Config.getConfig().dual:
        ltl_assumptions = [
            massage_ltl_for_dual(f, [c for c, _ in program.env_events], False)
            for f in ltl_assumptions
        ]
        ltl_guarantees = [
            massage_ltl_for_dual(f, [c for c, _ in program.env_events], False)
            for f in ltl_guarantees
        ]
        ltl_guarantees = [
            neg(
                implies(
                    conjunct_formula_set(ltl_assumptions),
                    conjunct_formula_set(ltl_guarantees),
                )
            )
        ]
        ltl_assumptions = []

    if config.Config.getConfig().dual2:
        ltl_assumptions = [
            massage_ltl_for_dual(f, program.num_in_out + program.bool_in_out, False)
            for f in ltl_assumptions
        ]
        ltl_guarantees = [
            massage_ltl_for_dual(f, program.num_in_out + program.bool_in_out, False)
            for f in ltl_guarantees
        ]

    in_acts = [e for e, t in program.env_events if t == BOOLEAN]
    out_acts = [c for c, t in program.con_events if t == BOOLEAN]
    prog_acts = program.out_events

    if tlsf_path is not None:
        if any(x for x in in_acts + prog_acts if x not in in_acts_syfco):
            raise Exception("TLSF file has different input variables than the program.")

        if any(x for x in out_acts if x not in out_acts_syfco):
            raise Exception(
                "TLSF file has different output variables than the program."
            )
    return ltl_assumptions, ltl_guarantees, in_acts, out_acts


def abstract_synthesis_loop(
    program: Program,
    ltl_assumptions: list[Formula],
    ltl_guarantees: list[Formula],
    original_ltl: Formula,
    in_acts: list[Variable],
    out_acts: list[Variable],
    bound: int,
) -> WrappedHOA:
    logging.info(
        program.to_prog(
            implies(
                conjunct_formula_set(ltl_assumptions),
                conjunct_formula_set(ltl_guarantees),
            )
        )
    )

    allow_user_input: bool = False
    prefer_lasso_counterexamples: bool = False

    (
        new_state_preds,
        ltl_assumptions,
        ltl_guarantees,
        signatures,
        old_to_new_st_preds,
    ) = extract_init_preds(program, ltl_assumptions, ltl_guarantees)

    ltl_abstraction_type: LTLAbstractionType = LTLAbstractionType(
        LTLAbstractionBaseType.effects_representation,
        LTLAbstractionTransitionType.one_trans,
        LTLAbstractionStructureType.control_state,
        LTLAbstractionOutputType.no_output,
    )

    LTL_problem = LTLSynthesisProblem(
        in_acts, out_acts, ltl_assumptions, ltl_guarantees
    )

    predicate_abstraction = EffectsAbstraction(program, old_to_new_st_preds)
    logging.info(
        "Abstraction backend: " + str(config.Config.getConfig().abstraction_backend)
    )

    new_tran_preds: set[Formula] = set()
    new_ranking_constraints: list[Formula] = []
    new_structural_loop_constraints: list[Formula] = []

    file_name_template = generate_tlsf_file_name_template()
    cegar_loop_counter = -1
    loop_counter = 0
    in_loop_vars = []

    def verify_if_requested(
        current_wrapped_hoa: WrappedHOA,
        current_predicate_abstraction: EffectsAbstraction,
        current_abstract_ltl_problem: AbstractLTLSynthesisProblem,
    ) -> None:
        if not config.Config.getConfig().verify_controller:
            return

        base_ltl_spec = (
            original_ltl
            if config.Config.getConfig().dual2
            else implies(
                conjunct_formula_set(ltl_assumptions),
                conjunct_formula_set(ltl_guarantees),
            )
        )
        machine = current_wrapped_hoa.machine
        should_negate = (
            config.Config.getConfig().dual and isinstance(machine, MealyMachine)
        ) or (not config.Config.getConfig().dual and isinstance(machine, MooreMachine))
        original_ltl_spec = neg(base_ltl_spec) if should_negate else base_ltl_spec

        logging.info("Verifying: " + str(original_ltl_spec))
        print(str(original_ltl_spec))
        role = "counterstrategy" if should_negate else "controller"
        print(
            "Verifying whether "
            + role
            + " enforces required LTL specification on program.."
        )
        verify_strategy(
            program,
            current_predicate_abstraction,
            current_wrapped_hoa.machine,
            original_ltl_spec,
            current_abstract_ltl_problem,
        )

    print("Starting abstract synthesis loop.")
    while bound != 0:
        bound -= 1
        cegar_loop_counter += 1
        new_state_preds = {strip_mathexpr(p) for p in new_state_preds}
        new_state_preds = {
            p
            for p in new_state_preds
            if p not in predicate_abstraction.raw_state_predicates
        }
        new_tran_preds = {
            strip_mathexpr(p)
            for p in set(new_tran_preds)
            if p not in predicate_abstraction.raw_transition_predicates
        }

        ## update predicate abstraction
        start = time.time()
        (_, abstract_ltl_problem) = refining_abs_and_log(
            predicate_abstraction,
            new_state_preds,
            new_tran_preds,
            new_ranking_constraints,
            new_structural_loop_constraints,
            in_loop_vars,
            signatures,
            LTL_problem,
            ltl_abstraction_type,
        )
        took = str(time.time() - start)
        logging.info("predicate abstraction took " + took + " seconds")
        print("predicate abstraction took " + took + " seconds")

        start = time.time()
        print("running LTL synthesis")

        safe_overwrite_if_logging(
            file_name_template, str(cegar_loop_counter), abstract_ltl_problem.tlsf
        )

        wrapped_hoa: WrappedHOA = ltl_synthesis.ltl_synthesis(
            abstract_ltl_problem, predicate_abstraction.symbol_table
        )
        base_ltl_spec = (
            original_ltl
            if config.Config.getConfig().dual2 and original_ltl is not None
            else implies(
                conjunct_formula_set(ltl_assumptions),
                conjunct_formula_set(ltl_guarantees),
            )
        )
        wrapped_hoa.verification_context = {
            "program": program,
            "base_ltl_spec": base_ltl_spec,
            "predicate_abstraction": predicate_abstraction,
            "abstract_ltl_problem": abstract_ltl_problem,
        }
        took = str(time.time() - start)
        logging.info("abstract ltl synthesis took " + took + " seconds")
        print("abstract ltl synthesis took " + took + " seconds")

        logging.info(
            "Peak memory used so far: "
            + str(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        )
        print(
            "Peak memory used so far: "
            + str(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        )

        if (wrapped_hoa.realisable and not config.Config.getConfig().dual2) or (
            not wrapped_hoa.realisable and config.Config.getConfig().dual2
        ):
            new_index = "-unreal" if config.Config.getConfig().dual else "-real"
            safe_rename_logging(file_name_template, str(cegar_loop_counter), new_index)

            verify_if_requested(
                wrapped_hoa, predicate_abstraction, abstract_ltl_problem
            )
            print_binary_rep_tables_at_end(program, predicate_abstraction)
            return wrapped_hoa

        if config.Config.getConfig().finite_synthesis:
            verify_if_requested(
                wrapped_hoa, predicate_abstraction, abstract_ltl_problem
            )
            print_binary_rep_tables_at_end(program, predicate_abstraction)
            return wrapped_hoa

        ## compatibility checking
        compatible, result = refinement_standard(
            program,
            predicate_abstraction,
            wrapped_hoa.machine,
            wrapped_hoa.realisable,
            signatures,
            loop_counter,
            abstract_ltl_problem,
            allow_user_input,
        )

        if compatible:
            if config.Config.getConfig().dual:
                new_index = "-real"
            else:
                new_index = "-unreal"
            safe_rename_logging(file_name_template, str(cegar_loop_counter), new_index)
            verify_if_requested(
                wrapped_hoa, predicate_abstraction, abstract_ltl_problem
            )
            print_binary_rep_tables_at_end(program, predicate_abstraction)
            return wrapped_hoa
        else:
            (
                (new_state_preds, new_tran_preds),
                new_ranking_constraints,
                new_structural_loop_constraints,
                in_loop_vars,
                loop_counter,
            ) = result
            if not (
                len(new_state_preds) > 0
                or len(new_tran_preds) > 0
                or len(new_ranking_constraints) > 0
            ):
                raise Exception(
                    "No new predicates or constraints found, but not compatible. Error in tool, "
                    "or program is non-deterministic."
                )

    raise Exception(
        f"Could not find a controller or counterstrategy with {cegar_loop_counter + 1} iterations."
    )


def print_binary_rep_tables_at_end(
    program: Program, predicate_abstraction: EffectsAbstraction
):
    seen = set()
    for table in program.get_binary_rep_tables():
        if table in seen:
            continue
        print(table)
        seen.add(table)

    if hasattr(predicate_abstraction, "get_binary_rep_tables"):
        for table in predicate_abstraction.get_binary_rep_tables():
            if table in seen:
                continue
            print(table)
            seen.add(table)


def generate_tlsf_file_name_template() -> str | None:
    if config.Config.getConfig().log:
        tlsf_files_path = str(
            os.path.join(
                config.Config.getConfig().log,
                "tlsf_files/",
            )
        )
        Path(tlsf_files_path).mkdir(parents=True, exist_ok=True)

        return str(os.path.join(tlsf_files_path, config.Config.getConfig().name + "-"))

    return None


def safe_overwrite_if_logging(file_name_template: str, counter: str, text: str):
    if config.Config.getConfig().log:
        file_name = file_name_template + counter
        try:
            os.remove(file_name)
        except OSError:
            pass
        with open(file_name, "w") as f:
            f.write(text)


def safe_rename_logging(file_name_template: str, counter: str, new_index: str):
    if config.Config.getConfig().log:
        os.rename(file_name_template + counter, file_name_template + new_index)


def refining_abs_and_log(
    predicate_abstraction: EffectsAbstraction,
    new_state_preds: set[Formula],
    new_tran_preds: set[Formula],
    new_ranking_constraints: list[Formula],
    new_structural_loop_constraints: list[Formula],
    in_loop_vars: list[Variable],
    signatures,
    original_LTL_problem: LTLSynthesisProblem,
    ltl_abstraction_type: LTLAbstractionType,
) -> Tuple[EffectsAbstraction, AbstractLTLSynthesisProblem]:
    print(
        "adding "
        + ", ".join(map(str, new_state_preds | new_tran_preds))
        + " to predicate abstraction"
    )

    predicate_abstraction.add_predicates(
        new_state_preds | new_tran_preds, set(), signatures, True
    )
    predicate_abstraction.add_ranking_constraints(new_ranking_constraints)
    predicate_abstraction.add_structural_loop_constraints(
        in_loop_vars, new_structural_loop_constraints
    )

    for table in predicate_abstraction.get_binary_rep_tables():
        logging.info(table)

    new_state_preds.clear()
    new_tran_preds.clear()
    new_ranking_constraints.clear()
    new_structural_loop_constraints.clear()

    abstract_ltl_problem = effects_to_ltl.to_ltl(
        predicate_abstraction, original_LTL_problem, ltl_abstraction_type
    )

    return predicate_abstraction, abstract_ltl_problem


def extract_init_preds(
    program: Program,
    ltl_assumptions: list[Formula],
    ltl_guarantees: list[Formula],
) -> Tuple[
    set[Formula],
    list[Formula],
    list[Formula],
    set[Formula],
    dict[Formula, Formula],
    set[Formula],
]:
    new_state_preds = set()

    if config.Config.getConfig().finite_synthesis:
        for var in program.local_vars:
            for pred in finite_state_preds(var, program.symbol_table[var.name]):
                new_state_preds.add(pred)
    else:
        for v, v_type in program.init_var_values.items():
            if v_type == BOOLEAN:
                new_state_preds.add(Variable(v))

    env_con_events = set(program.bool_in_out)

    for t in program.transitions:
        preds_in_cond = atomic_predicates(t.condition)
        for p in preds_in_cond:
            if p not in env_con_events:
                new_state_preds.add(p)
        in_outs_in_act = {
            v for v in program.bool_in_out for act in t.action if v in act.variablesin()
        }
        for p in in_outs_in_act:
            new_state_preds.add(p)

        for act in t.action:
            # if updating a boolean, add atomic predicates of the right-hand side
            if program.symbol_table[str(act.left)] == BOOLEAN:
                for p in atomic_predicates(act.right):
                    new_state_preds.add(p)

    ltl_assumptions = [
        strip_mathexpr(ltl).replace_vars(
            lambda x: program.constants[x] if x in program.constants.keys() else x
        )
        for ltl in ltl_assumptions
    ]
    ltl_guarantees = [
        strip_mathexpr(ltl).replace_vars(
            lambda x: program.constants[x] if x in program.constants.keys() else x
        )
        for ltl in ltl_guarantees
    ]

    for f in ltl_assumptions:
        for p in atomic_predicates(f):
            new_state_preds.add(p)
    for f in ltl_guarantees:
        for p in atomic_predicates(f):
            new_state_preds.add(p)

    # TODO don't normalise here; normalise inside of effectsabstraction
    # rankings should also be added inside of abstraction, based on normalised preds?
    old_to_new_st_preds = {}
    symbol_table = program.symbol_table
    signatures = set()
    normalised_state_preds = set()

    for p in new_state_preds:
        if p in program.bool_in_out:
            continue
        if len(p.variablesin()) == 0:
            print("flattened: " + str(p))
            old_to_new_st_preds[p] = (
                Value(BoolAtoms.TRUE)
                if sat(p, symbol_table)
                else Value(BoolAtoms.FALSE)
            )
        if isinstance(p, Variable):
            if p.name in program.states:
                continue
            normalised_state_preds.add(p)
            continue
        result = normalise_pred_multiple_vars(p, signatures, symbol_table)
        if isinstance(result, Variable):
            normalised_state_preds.add(pred)
        # these will be formulas over boolean vars
        elif isinstance(result, Formula):
            continue
        else:
            sig, new_p, preds = result
            old_to_new_st_preds[p] = new_p
            signatures.add(sig)
            normalised_state_preds.update(preds)

    new_state_preds = set()
    filtered = {}
    for x in normalised_state_preds:
        if is_tautology(x, symbol_table):
            filtered[x] = true()
        elif is_contradictory(x, symbol_table):
            filtered[x] = false()
        else:
            new_state_preds.add(x)

    new_old_to_new_st_preds = {}
    for k, v in old_to_new_st_preds.items():
        new_old_to_new_st_preds[k] = v.replace_formulas(filtered)

    old_to_new_st_preds = new_old_to_new_st_preds
    new_ltl_assumptions = [
        l.replace_formulas(old_to_new_st_preds) for l in ltl_assumptions
    ]
    new_ltl_guarantees = [
        l.replace_formulas(old_to_new_st_preds) for l in ltl_guarantees
    ]

    return (
        new_state_preds,
        new_ltl_assumptions,
        new_ltl_guarantees,
        signatures,
        old_to_new_st_preds,
    )
