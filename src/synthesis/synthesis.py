import logging
import os
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
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.compatibility_checking.compatibility_checking_con import (
    compatibility_checking_con,
)
from analysis.refinement.refinement import refinement_standard
from parsing.string_to_ltl import string_to_ltl
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (
    true,
    atomic_predicates,
    finite_state_preds,
    strip_mathexpr,
    normalise_pred_multiple_vars,
    normalise_formula,
    conjunct_formula_set,
    implies,
    massage_ltl_for_dual,
    neg,
)
from prop_lang.variable import Variable
from synthesis.ltl_synthesis import (
    ltl_synthesis,
    syfco_ltl,
    syfco_ltl_in,
    syfco_ltl_out,
)
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from pathlib import Path

from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.wrapped_hoa import WrappedHOA


def synthesize(
    program: Program,
    ltl: Formula | None,
    tlsf_path: str | None,
) -> WrappedHOA:
    if not program.deterministic:
        print("Program is non-deterministic; refinement may fail.")

    start = time.time()
    (
        ltl_assumptions,
        ltl_guarantees,
        in_acts,
        out_acts,
    ) = process_specifications(program, ltl, tlsf_path)
    aps = set()
    for ltl in (ltl_assumptions, ltl_guarantees):
        for x in ltl:
            aps |= atomic_predicates(x)

    msg = f"spec contains {len(aps)} APs ({[str(a) for a in aps]})"
    print(msg)
    logging.info(msg)

    wrapped_hoa: WrappedHOA = abstract_synthesis_loop(
        program,
        ltl_assumptions,
        ltl_guarantees,
        in_acts,
        out_acts,
    )
    logging.info("synthesis took " + str(time.time() - start))
    return wrapped_hoa


def process_specifications(
    program: Program, ltl: Formula | None, tlsf_path: str | None
):
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if ' Error"' in ltl_text:
            raise Exception(
                "Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text
            )
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)

        ltl = string_to_ltl(ltl_text)
    else:
        in_acts_syfco = []
        out_acts_syfco = []

    if isinstance(ltl, BiOp) and (ltl.op == "->" or ltl.op == "=>"):
        ltl_assumptions_formula = ltl.left
        ltl_guarantees_formula = ltl.right
    else:
        ltl_assumptions_formula = true()
        ltl_guarantees_formula = ltl

    if (
        isinstance(ltl_assumptions_formula, BiOp)
        and ltl_assumptions_formula.op[0] == "&"
    ):
        ltl_assumptions = ltl_assumptions_formula.sub_formulas_up_to_associativity()
    else:
        ltl_assumptions = [ltl_assumptions_formula]

    if isinstance(ltl_guarantees_formula, BiOp) and ltl_guarantees_formula.op[0] == "&":
        ltl_guarantees = ltl_guarantees_formula.sub_formulas_up_to_associativity()
    else:
        ltl_guarantees = [ltl_guarantees_formula]

    if config.Config.getConfig().dual:
        ltl_assumptions = [
            massage_ltl_for_dual(f, program.env_events) for f in ltl_assumptions
        ]
        ltl_guarantees = [
            massage_ltl_for_dual(f, program.env_events) for f in ltl_guarantees
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

    in_acts = [e for e in program.env_events]
    out_acts = [e for e in program.con_events]
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
    in_acts: list[Variable],
    out_acts: list[Variable],
) -> WrappedHOA:
    allow_user_input: bool = False
    prefer_lasso_counterexamples: bool = False

    (
        new_state_preds,
        ltl_assumptions,
        ltl_guarantees,
        signatures,
        old_to_new_st_preds,
    ) = extract_init_preds(program, ltl_assumptions, ltl_guarantees, in_acts, out_acts)

    ltl_abstraction_type: LTLAbstractionType = LTLAbstractionType(
        LTLAbstractionBaseType.effects_representation,
        LTLAbstractionTransitionType.one_trans,
        LTLAbstractionStructureType.control_state,
        LTLAbstractionOutputType.no_output,
    )

    original_LTL_problem = LTLSynthesisProblem(
        in_acts, out_acts, ltl_assumptions, ltl_guarantees
    )

    predicate_abstraction = EffectsAbstraction(program, old_to_new_st_preds)

    new_tran_preds: set[Formula] = set()
    new_ranking_constraints: list[Formula] = []
    new_structural_loop_constraints: list[Formula] = []

    file_name_template: str = generate_tlsf_file_name_template()
    loop_counter: int = -1

    print("Starting abstract synthesis loop.")
    while True:
        loop_counter += 1
        new_state_preds = {strip_mathexpr(p) for p in new_state_preds}
        new_state_preds = {
            p
            for p in new_state_preds
            if p not in predicate_abstraction.state_predicates
            and p not in predicate_abstraction.chain_state_predicates
        }
        new_tran_preds = {
            strip_mathexpr(p)
            for p in set(new_tran_preds)
            if p not in predicate_abstraction.transition_predicates
        }

        ## update predicate abstraction
        start = time.time()
        (base_abstraction, abstract_ltl_problem) = refining_abs_and_log(
            predicate_abstraction,
            new_state_preds,
            new_tran_preds,
            new_ranking_constraints,
            new_structural_loop_constraints,
            original_LTL_problem,
            ltl_abstraction_type,
        )
        logging.info("refining predicate abstraction took " + str(time.time() - start))

        start = time.time()
        print("running LTL synthesis")

        safe_overwrite_if_logging(
            file_name_template, str(loop_counter), abstract_ltl_problem.tlsf
        )

        wrapped_hoa: WrappedHOA = ltl_synthesis(
            abstract_ltl_problem, predicate_abstraction.symbol_table
        )
        logging.info("ltl synthesis took " + str(time.time() - start))

        if wrapped_hoa.is_controller:
            new_index = "-unreal" if config.Config.getConfig().dual else "-real"
            safe_rename_logging(file_name_template, str(loop_counter), new_index)

            if config.Config.getConfig().verify_controller:
                original_ltl_spec = implies(
                    conjunct_formula_set(ltl_assumptions),
                    conjunct_formula_set(ltl_guarantees),
                )
                print(str(original_ltl_spec))
                print(
                    "Verifying whether "
                    + (
                        "controller"
                        if config.Config.getConfig().dual
                        else "counterstrategy"
                    )
                    + " enforces required LTL specification on program.."
                )
                compatibility_checking_con(
                    program,
                    predicate_abstraction,
                    wrapped_hoa.machine,
                    original_ltl_spec,
                )

            return wrapped_hoa

        if config.Config.getConfig().finite_synthesis:
            return wrapped_hoa

        ## compatibility checking
        compatible, result = refinement_standard(
            program,
            predicate_abstraction,
            wrapped_hoa.machine,
            wrapped_hoa.is_controller,
            signatures,
            loop_counter,
            prefer_lasso_counterexamples,
            allow_user_input,
        )

        if compatible:
            if config.Config.getConfig().dual:
                new_index = "-real"
                if config.Config.getConfig().verify_controller:
                    print("Controller enforces the required LTL property!")
            else:
                new_index = "-unreal"
            safe_rename_logging(file_name_template, str(loop_counter), new_index)
            return wrapped_hoa
        else:
            (
                (new_state_preds, new_tran_preds),
                new_ranking_constraints,
                new_structural_loop_constraints,
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


def safe_overwrite_if_logging(file_name_template, counter, text):
    if config.Config.getConfig().log:
        file_name = file_name_template + counter
        try:
            os.remove(file_name)
        except OSError:
            pass
        with open(file_name, "w") as f:
            f.write(text)


def safe_rename_logging(file_name_template, counter, new_index):
    if config.Config.getConfig().log:
        os.rename(file_name_template + counter, file_name_template + new_index)


def refining_abs_and_log(
    predicate_abstraction: EffectsAbstraction,
    new_state_preds: set[Formula],
    new_tran_preds: set[Formula],
    new_ranking_constraints: list[Formula],
    new_structural_loop_constraints: list[Formula],
    original_LTL_problem: LTLSynthesisProblem,
    ltl_abstraction_type: LTLAbstractionType,
):
    print(
        "adding "
        + ", ".join(map(str, new_state_preds | new_tran_preds))
        + " to predicate abstraction"
    )

    predicate_abstraction.add_predicates(new_state_preds | new_tran_preds, set(), True)
    predicate_abstraction.add_ranking_constraints(new_ranking_constraints)
    predicate_abstraction.add_structural_loop_constraints(
        new_structural_loop_constraints
    )

    new_state_preds.clear()
    new_tran_preds.clear()
    new_ranking_constraints.clear()
    new_structural_loop_constraints.clear()

    base_abstraction, abstract_ltl_problem = effects_to_ltl.to_ltl(
        predicate_abstraction, original_LTL_problem, ltl_abstraction_type
    )

    return base_abstraction, abstract_ltl_problem


def extract_init_preds(
    program: Program,
    ltl_assumptions: list[Formula],
    ltl_guarantees: list[Formula],
    in_acts: list[Variable],
    out_acts: list[Variable],
):
    new_state_preds = set()

    if config.Config.getConfig().finite_synthesis:
        new_state_preds.update(
            {pred for val in program.valuation for pred in finite_state_preds(val)}
        )
    else:
        new_state_preds.update(
            Variable(b.name)
            for b in program.valuation
            if b.type.lower().startswith("bool")
        )

    env_con_events = set(program.con_events + program.env_events)

    for t in program.transitions:
        preds_in_cond = atomic_predicates(t.condition)
        new_state_preds.update(p for p in preds_in_cond if p not in env_con_events)
        for act in t.action:
            if len(act.right.variablesin()) == 0:
                if program.symbol_table[str(act.left)].type.startswith("bool"):
                    new_state_preds.add(act.left)
                else:
                    new_state_preds.add(BiOp(act.left, "=", act.right))

    # TODO don't normalise here; normalise inside of effectsabstraction
    # rankings should also be added inside of abstraction, based on normalised preds?
    old_to_new_st_preds = {}
    symbol_table = program.symbol_table
    signatures = set()
    normalised_state_preds = set()
    for p in new_state_preds:
        if isinstance(p, Variable):
            normalised_state_preds.add(p)
            continue
        result = normalise_pred_multiple_vars(p, signatures, symbol_table)
        if len(result) == 1:
            normalised_state_preds.add(result)
        else:
            sig, new_p, preds = result
            old_to_new_st_preds[p] = new_p
            signatures.add(sig)
            normalised_state_preds.update(preds)
    new_state_preds = normalised_state_preds

    prog_state_vars = [Variable(s) for s in program.states]
    new_ltl_assumptions = []
    ignore_these = set(in_acts + out_acts + prog_state_vars)
    for ltl in ltl_assumptions:
        ltl = strip_mathexpr(ltl)
        ltl = ltl.replace_vars(
            lambda x: program.constants[x] if x in program.constants.keys() else x
        )
        new_ltl, new_preds = normalise_formula(
            ltl, signatures, symbol_table, ignore_these
        )
        new_state_preds.update(new_preds)
        new_ltl_assumptions.append(new_ltl)

    new_ltl_guarantees = []
    for ltl in ltl_guarantees:
        ltl = strip_mathexpr(ltl)
        ltl = ltl.replace_vars(
            lambda x: program.constants[x] if x in program.constants.keys() else x
        )
        new_ltl, new_preds = normalise_formula(
            ltl, signatures, symbol_table, ignore_these
        )
        new_state_preds.update(new_preds)
        new_ltl_guarantees.append(new_ltl)

    return (
        new_state_preds,
        new_ltl_assumptions,
        new_ltl_guarantees,
        signatures,
        old_to_new_st_preds,
    )
