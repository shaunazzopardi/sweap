import logging
import time
import analysis.abstraction.effects_abstraction.effects_to_ltl as effects_to_ltl
import config

from typing import Tuple
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
from analysis.compatibility_checking.compatibility_checking_con import (
    compatibility_checking_con,
)
from analysis.refinement.refinement import refinement_standard
from parsing.string_to_ltl import string_to_ltl
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (
    true,
    stringify_formula,
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
from synthesis.machines.mealy_machine import MealyMachine


def synthesize(
    program: Program,
    ltl: Formula,
    tlsf_path: str,
    docker: bool,
    project_on_abstraction=False,
) -> Tuple[bool, MealyMachine]:
    # if not program.deterministic:
    #     raise Exception("We do not handle non-deterministic programs yet.")

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

    result = abstract_synthesis_loop(
        program,
        ltl_assumptions,
        ltl_guarantees,
        in_acts,
        out_acts,
    )
    logging.info("synthesis took " + str(time.time() - start))
    return result


def process_specifications(program, ltl, tlsf_path):
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
    ltl_assumptions: [Formula],
    ltl_guarantees: [Formula],
    in_acts: [Variable],
    out_acts: [Variable],
) -> Tuple[bool, MealyMachine]:
    eager = False
    keep_only_bool_interpolants = False
    allow_user_input = False
    conservative_with_state_predicates = False
    prefer_lasso_counterexamples = False

    # TODO when we have a predicate mismatch we also need some information about the guard of the transition being taken
    #  by the program since some information about why the environment chose the wrong predicates is hidden there
    #  a solution here may be to use the atomic predicates appearing the in the transition guard as state predicates

    add_all_boolean_vars = True
    env_con_events = set(program.con_events + program.env_events)

    new_state_preds = set()

    if config.Config.getConfig().finite_synthesis:
        new_state_preds.update(
            {pred for val in program.valuation for pred in finite_state_preds(val)}
        )
    else:
        if add_all_boolean_vars:
            new_state_preds.update(
                Variable(b.name)
                for b in program.valuation
                if b.type.lower().startswith("bool")
            )

    # if config.Config.getConfig().add_all_preds_in_prog:
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

    # new_state_preds = set(itertools.chain.from_iterable(map(lambda x: x[1], map(normalise_predicate, set(new_state_preds)))))

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

    ltl_assumptions = new_ltl_assumptions
    ltl_guarantees = new_ltl_guarantees

    new_tran_preds = set()
    new_ranking_constraints = []
    new_structural_loop_constraints = []

    loop_counter = 0

    ltlAbstractionType: LTLAbstractionType = LTLAbstractionType(
        LTLAbstractionBaseType.effects_representation,
        LTLAbstractionTransitionType.one_trans,
        LTLAbstractionStructureType.control_state,
        LTLAbstractionOutputType.no_output,
    )

    predicate_abstraction = EffectsAbstraction(program, old_to_new_st_preds)

    original_LTL_problem = LTLSynthesisProblem(
        in_acts, out_acts, ltl_assumptions, ltl_guarantees
    )

    print("Starting abstract synthesis loop.")

    print(str(len(new_state_preds)) + ": " + ", ".join(map(str, new_state_preds)))
    while True:
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
        print(
            str(len(new_state_preds | new_tran_preds))
            + ": "
            + ", ".join(map(str, new_state_preds | new_tran_preds))
        )
        print(
            "adding "
            + ", ".join(map(str, new_state_preds | new_tran_preds))
            + " to predicate abstraction"
        )
        predicate_abstraction.add_predicates(
            new_state_preds | new_tran_preds, set(), True
        )
        logging.info(
            "adding "
            + ", ".join(map(str, new_state_preds | new_tran_preds))
            + " to predicate abstraction"
            + " took "
            + str(time.time() - start)
        )

        predicate_abstraction.add_ranking_constraints(new_ranking_constraints)
        predicate_abstraction.add_structural_loop_constraints(
            new_structural_loop_constraints
        )

        new_state_preds.clear()
        new_tran_preds.clear()
        new_ranking_constraints.clear()
        new_structural_loop_constraints.clear()

        ## LTL abstraction
        start = time.time()
        print("constructing LTL abstraction")
        base_abstraction, abstract_ltl_problem = effects_to_ltl.to_ltl(
            predicate_abstraction, original_LTL_problem, ltlAbstractionType
        )

        logging.info("to ltl abstraction took " + str(time.time() - start))

        start = time.time()
        print("running LTL synthesis")
        (real, mm_hoa) = ltl_synthesis(abstract_ltl_problem)
        logging.info("ltl synthesis took " + str(time.time() - start))

        if real and not debug:
            if config.Config.getConfig().verify_controller:
                print("massaging abstract controller")
                mm = predicate_abstraction.massage_mealy_machine(
                    mm_hoa,
                    base_abstraction,
                    ltlAbstractionType,
                    abstract_ltl_problem,
                    real,
                )
                if config.Config.getConfig().dual:
                    mm = mm.to_moore_machine()
                    logging.info("Unrealizable")
                else:
                    logging.info("Realizable")

                original_ltl_spec = implies(
                    conjunct_formula_set(ltl_assumptions),
                    conjunct_formula_set(ltl_guarantees),
                )
                compatibility_checking_con(
                    program, predicate_abstraction, mm, original_ltl_spec
                )
                return True, "\n".join(mm_hoa.split("\n")[1:])
            else:
                return True, "\n".join(mm_hoa.split("\n")[1:])
        elif not real and config.Config.getConfig().finite_synthesis:
            return False, "\n".join(mm_hoa.split("\n")[1:])

        start = time.time()
        print("massaging abstract counterstrategy")
        mm = predicate_abstraction.massage_mealy_machine(
            mm_hoa,
            base_abstraction,
            ltlAbstractionType,
            abstract_ltl_problem,
            real,
        )

        logging.info(mm)
        logging.info("massaging mealy machine took " + str(time.time() - start))

        ## compatibility checking
        compatible, result = refinement_standard(
            program,
            predicate_abstraction,
            mm,
            real,
            signatures,
            loop_counter,
            prefer_lasso_counterexamples,
            allow_user_input,
            keep_only_bool_interpolants,
            conservative_with_state_predicates,
            eager,
        )

        if compatible:
            return False, "\n".join(mm_hoa.split("\n")[1:])
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


def write_counterexample(
    program,
    agreed_on_transitions: [(Transition, dict)],
    # disagreed_on_transitions: ([Transition], dict),
    program_actually_took: [(Transition, dict)],
):
    logging.info("Mismatch:")
    logging.info("Agreed on transitions:")
    for trans, state in [(t, s) for (t, s) in agreed_on_transitions]:
        vs = set(
            trans.condition.variablesin()
            + [v for v in list(state.keys()) if str(v).startswith("mon_")]
            + [v for v in list(state.keys()) if str(v).startswith("pred_")]
            + [v for v in program.env_events + program.con_events]
        )

        logging.info(
            "\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs])
        )
        logging.info(("env: " if "env" == state["turn"] else "con: ") + str(trans))

    logging.info("Environment did not want to take:")

    logging.info(
        ("env: " if "env" == program_actually_took[1]["turn"] else "con: ")
        + str(program_actually_took[0])
    )
    vs = []
    vs += set(
        program_actually_took[0].condition.variablesin()
        + [
            v
            for v in list(program_actually_took[1].keys())
            if str(v).startswith("mon_")
        ]
        + [
            v
            for v in list(program_actually_took[1].keys())
            if str(v).startswith("pred_")
        ]
        + [v for v in program.env_events + program.con_events]
    )
    logging.info(
        "with state: "
        + ", ".join([str(v) + "=" + program_actually_took[1][str(v)] for v in vs])
    )


def write_counterexample_state(
    program,
    agreed_on_transitions: [(Transition, dict)],
    disagreed_on_state: ([Formula], dict),
):
    logging.info("Mismatch:")
    logging.info("Agreed on transitions:")
    for trans, state in [(t, s) for (t, s) in agreed_on_transitions]:
        vs = set(
            trans.condition.variablesin()
            + [v for v in list(state.keys()) if str(v).startswith("mon_")]
            + [v for v in list(state.keys()) if str(v).startswith("pred_")]
            + [v for v in program.env_events + program.con_events]
        )

        logging.info(
            "\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs])
        )
        logging.info(("env: " if "env" == state["turn"] else "con: ") + str(trans))

    logging.info("Environment wanted state to satisfy:")

    logging.info(", ".join([str(p) for p in disagreed_on_state[0]]))

    logging.info("Program however has state:")
    logging.info(", ".join([v + " = " + k for v, k in disagreed_on_state[1].items()]))
