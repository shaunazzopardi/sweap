import logging
import config
import time
from typing import Tuple

from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionStructureType, \
    LTLAbstractionTransitionType, LTLAbstractionBaseType, LTLAbstractionType, LTLAbstractionOutputType
from analysis.compatibility_checking.compatibility_checking import compatibility_checking
from analysis.refinement.fairness_refinement.ranking_refinement import ranking_refinement, \
    ranking_refinement_both_sides, already_an_equivalent_ranking

from parsing.string_to_ltl import string_to_ltl
from programs.program import Program
from analysis.refinement.fairness_refinement.fairness_util import try_liveness_refinement
from analysis.refinement.safety_refinement.interpolation_refinement import safety_refinement_seq_int
from programs.util import reduce_up_to_iff
from prop_lang.mathexpr import MathExpr
from prop_lang.value import Value
from synthesis.ltl_synthesis import ltl_synthesis, syfco_ltl, syfco_ltl_in, syfco_ltl_out
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from synthesis.mealy_machine import MealyMachine
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import true, stringify_formula, should_be_math_expr, normalise_mathexpr, ranking_from_predicate, \
    atomic_predicates, finite_state_preds, strip_outer_mathexpr
from prop_lang.variable import Variable

import analysis.abstraction.effects_abstraction.effects_to_ltl as effects_to_ltl


def finite_state_synth(program: Program,
                       ltl: Formula,
                       tlsf_path: str) -> Tuple[bool, MealyMachine]:
    if not program.is_finite_state():
        raise Exception("Cannot use strix, problem is not finite-state.")

    print("constructing initial abstraction")
    start = time.time()
    preds = [
        pred
        for val in program.valuation
        for pred in finite_state_preds(val)]

    abstr = EffectsAbstraction(program)
    ltl_assumptions, ltl_guarantees, in_acts, out_acts = process_specifications(program, ltl, tlsf_path)
    new_ltl_assumptions = []
    for ltl in ltl_assumptions:
        new_ltl, new_preds = stringify_formula(ltl, in_acts + out_acts)
        preds += new_preds
        new_ltl_assumptions.append(new_ltl)

    new_ltl_guarantees = []
    for ltl in ltl_guarantees:
        new_ltl, new_preds = stringify_formula(ltl, in_acts + out_acts)
        preds += new_preds
        new_ltl_guarantees.append(new_ltl)

    ltl_assumptions = new_ltl_assumptions
    ltl_guarantees = new_ltl_guarantees

    abstr.add_predicates(preds, {})
    logging.info(f"initial abstraction took {time.time() - start}")

    start = time.time()
    print("constructing LTL abstraction")
    original_LTL_problem = LTLSynthesisProblem(
        in_acts,
        out_acts,
        ltl_assumptions,
        ltl_guarantees)

    ltlAbstractionType: LTLAbstractionType = LTLAbstractionType(
        LTLAbstractionBaseType.effects_representation,
        LTLAbstractionTransitionType.one_trans,
        LTLAbstractionStructureType.control_state,
        LTLAbstractionOutputType.no_output)

    _, abstract_ltl_problem = effects_to_ltl.to_ltl(
        abstr,
        original_LTL_problem,
        ltlAbstractionType)
    logging.info(f"to ltl abstraction took {time.time() - start}")

    print("running LTL synthesis")
    start = time.time()
    (real, mm_hoa) = ltl_synthesis(abstract_ltl_problem)
    logging.info("synthesis took " + str(time.time() - start))
    return (real, mm_hoa)


def synthesize(program: Program,
               ltl: Formula,
               tlsf_path: str,
               docker: bool,
               project_on_abstraction=False) -> Tuple[bool, MealyMachine]:
    # if not program.deterministic:
    #     raise Exception("We do not handle non-deterministic programs yet.")

    start = time.time()
    ltl_assumptions, ltl_guarantees, in_acts, out_acts = process_specifications(program, ltl, tlsf_path)
    aps = set()
    for ltl in (ltl_assumptions, ltl_guarantees):
        for x in ltl:
            aps |= atomic_predicates(x)

    msg = f"spec contains {len(aps)} APs ({[str(a) for a in aps]})"
    print(msg)
    logging.info(msg)

    result = abstract_synthesis_loop(program, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker,
                                     project_on_abstraction=project_on_abstraction)
    logging.info("synthesis took " + str(time.time() - start))
    return result


def process_specifications(program, ltl, tlsf_path):
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if " Error\"" in ltl_text:
            raise Exception("Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text)
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

    if isinstance(ltl_assumptions_formula, BiOp) and ltl_assumptions_formula.op[0] == "&":
        ltl_assumptions = ltl_assumptions_formula.sub_formulas_up_to_associativity()
    else:
        ltl_assumptions = [ltl_assumptions_formula]

    if isinstance(ltl_guarantees_formula, BiOp) and ltl_guarantees_formula.op[0] == "&":
        ltl_guarantees = ltl_guarantees_formula.sub_formulas_up_to_associativity()
    else:
        ltl_guarantees = [ltl_guarantees_formula]

    in_acts = [e for e in program.env_events]
    out_acts = [e for e in program.con_events]
    prog_acts = program.out_events

    if tlsf_path is not None:
        if any(x for x in in_acts + prog_acts if x not in in_acts_syfco):
            raise Exception("TLSF file has different input variables than the program.")

        if any(x for x in out_acts if x not in out_acts_syfco):
            raise Exception("TLSF file has different output variables than the program.")
    return ltl_assumptions, ltl_guarantees, in_acts, out_acts


def abstract_synthesis_loop(program: Program, ltl_assumptions: [Formula], ltl_guarantees: [Formula], in_acts: [Variable],
                            out_acts: [Variable], docker: bool, project_on_abstraction=False, debug=False) -> \
        Tuple[bool, MealyMachine]:
    eager = False
    keep_only_bool_interpolants = False
    use_explicit_loops_abstraction = False
    allow_user_input = False
    choose_predicates = False
    conservative_with_state_predicates = False
    prefer_lasso_counterexamples = False
    add_tran_preds_immediately = config.Config.getConfig().eager_fairness
    add_tran_preds_after_state_abstraction = config.Config.getConfig().eager_fairness and not config.Config.getConfig().only_safety
    only_safety = False

    # TODO when we have a predicate mismatch we also need some information about the guard of the transition being taken
    #  by the program since some information about why the environment chose the wrong predicates is hidden there
    #  a solution here may be to use the atomic predicates appearing the in the transition guard as state predicates

    add_all_boolean_vars = True

    new_state_preds = []
    if add_all_boolean_vars:
        new_state_preds.extend([Variable(b.name) for b in program.valuation if b.type.lower().startswith("bool")])

    if config.Config.getConfig().add_all_preds_in_prog:
        for t in program.transitions:
            preds_in_cond = atomic_predicates(t.condition)
            new_state_preds.extend([p for p in preds_in_cond if p not in program.con_events + program.env_events])

    prog_state_vars = [Variable(s) for s in program.states]
    new_ltl_assumptions = []
    ltl_state_preds = []
    for ltl in ltl_assumptions:
        ltl = ltl.replace_formulas(normalise_mathexpr)
        new_ltl, preds = stringify_formula(ltl, in_acts + out_acts + prog_state_vars)
        ltl_state_preds += preds
        new_ltl_assumptions.append(new_ltl)

    new_ltl_guarantees = []
    for ltl in ltl_guarantees:
        ltl = ltl.replace_formulas(normalise_mathexpr)
        new_ltl, preds = stringify_formula(ltl, in_acts + out_acts + prog_state_vars)
        ltl_state_preds += preds
        new_ltl_guarantees.append(new_ltl)

    ltl_assumptions = new_ltl_assumptions
    ltl_guarantees = new_ltl_guarantees

    new_state_preds = (set(new_state_preds))

    new_tran_preds = set()
    new_ltl_constraints = set()

    rankings = []
    if config.Config.getConfig()._eager_fairness or config.Config.getConfig()._natural_fairness:
        for tv in program.valuation:
            if tv.type.lower().startswith("bool"):
                continue
            if tv.type.lower().startswith("int"):
                ranking = Variable(tv.name)
                pos_rk = BiOp(ranking, ">=", Value("0"))
                neg_rk = BiOp(ranking, "<=", Value("0"))
                invars_top = [neg_rk]
                invars_bot = [pos_rk]
                rankings += [ranking_refinement_both_sides(ranking, invars_bot, invars_top)]
            elif tv.type.lower().startswith("nat"):
                ranking = Variable(tv.name)
                invars = []
                rankings += [ranking_refinement(ranking, invars)]
            elif ".." in tv.type:
                ranking = Variable(tv.name)
                rankings += [ranking_refinement_both_sides(ranking, [], [])]

    loop_counter = 0

    ltlAbstractionType: LTLAbstractionType = LTLAbstractionType(LTLAbstractionBaseType.effects_representation,
                                                                LTLAbstractionTransitionType.one_trans,
                                                                LTLAbstractionStructureType.control_state,
                                                                LTLAbstractionOutputType.no_output)


    predicate_abstraction = EffectsAbstraction(program)

    original_LTL_problem = LTLSynthesisProblem(in_acts,
                                               out_acts,
                                               ltl_assumptions,
                                               ltl_guarantees)

    print("Starting abstract synthesis loop.")

    to_add_rankings_for = []

    new_new_state_preds = set(ltl_state_preds)
    for st_pred in new_state_preds:
        if isinstance(st_pred, MathExpr) or should_be_math_expr(st_pred):
            normalised = normalise_mathexpr(st_pred)
            if normalised is None:
                normalised = st_pred
            new_st_preds = atomic_predicates(normalised)
            new_new_state_preds = reduce_up_to_iff(new_new_state_preds, new_st_preds, predicate_abstraction.symbol_table)
        else:
            new_new_state_preds = reduce_up_to_iff(new_new_state_preds, [st_pred], predicate_abstraction.symbol_table)
    new_state_preds = new_new_state_preds
    while True:
        if add_tran_preds_immediately and not only_safety:
            to_add_rankings_for.extend(new_state_preds)
            for state_pred in to_add_rankings_for:
                if isinstance(state_pred, MathExpr) or should_be_math_expr(state_pred):
                    result = ranking_from_predicate(state_pred)
                    if result is None: continue
                    f, invar = result
                    rankings.append(ranking_refinement(f, [invar]))
            add_tran_preds_immediately = False

        done_rankings = set()
        for tran_preds, constraints in rankings:
            for finite_re, st_prds, ltl_constraints in constraints:
                if not already_an_equivalent_ranking(done_rankings, finite_re):
                    new_tran_preds.update(tran_preds)
                    new_state_preds.update(st_prds)
                    new_ltl_constraints.add(ltl_constraints)
                    done_rankings.add(finite_re)
        rankings.clear()
        to_add_rankings_for.clear()

        new_state_preds = {strip_outer_mathexpr(p) for p in new_state_preds}
        new_state_preds = {p for p in new_state_preds if p not in predicate_abstraction.state_predicates}
        new_tran_preds = {p for p in set(new_tran_preds) if p not in predicate_abstraction.transition_predicates}

        ## update predicate abstraction
        start = time.time()
        print("adding " + ", ".join(map(str, new_state_preds | new_tran_preds)) + " to predicate abstraction")
        predicate_abstraction.add_predicates(new_state_preds, new_tran_preds, True)
        logging.info("adding " + ", ".join(map(str, new_state_preds | new_tran_preds)) + " to predicate abstraction" + " took " + str(time.time() - start))

        predicate_abstraction.add_constraints(new_ltl_constraints)

        new_state_preds.clear()
        new_tran_preds.clear()
        new_ltl_constraints.clear()

        ## LTL abstraction
        start = time.time()
        print("constructing LTL abstraction")
        base_abstraction, abstract_ltl_problem = effects_to_ltl.to_ltl(predicate_abstraction,
                                                                       original_LTL_problem,
                                                                       ltlAbstractionType)

        logging.info("to ltl abstraction took " + str(time.time() - start))

        start = time.time()
        print("running LTL synthesis")
        (real, mm_hoa) = ltl_synthesis(abstract_ltl_problem)
        logging.info("ltl synthesis took " + str(time.time() - start))

        if real and not debug:
            logging.info("Realizable")
            if project_on_abstraction:
                # TODO actually project
                print("massaging abstract controller")
                mm = predicate_abstraction.massage_mealy_machine(mm_hoa,
                                                                 base_abstraction,
                                                                 ltlAbstractionType,
                                                                 abstract_ltl_problem,
                                                                 real)
                return True, mm
            else:
                return True, mm_hoa

        if add_tran_preds_after_state_abstraction:
            add_tran_preds_immediately = True
            to_add_rankings_for.extend(predicate_abstraction.state_predicates)

        start = time.time()
        print("massaging abstract counterstrategy")
        mm = predicate_abstraction.massage_mealy_machine(mm_hoa,
                                                         base_abstraction,
                                                         ltlAbstractionType,
                                                         abstract_ltl_problem,
                                                         real)

        logging.info(mm)
        logging.info("massaging mealy machine took " + str(time.time() - start))

        ## compatibility checking
        start = time.time()

        print("checking for compatibility of counterstrategy with program")
        determination, result = compatibility_checking(program,
                                                       predicate_abstraction,
                                                       mm,
                                                       real,
                                                       base_abstraction,
                                                       ltlAbstractionType,
                                                       project_on_abstraction,
                                                       prefer_lasso_counterexamples)

        logging.info("compatibility checking took " + str(time.time() - start))

        if determination == False:
            logging.info("Problem is unrealisable.")
            return False, mm
        elif determination == True:
            raise Exception("error")
        else:
            agreed_on_execution, disagreed_on_state = result

        # write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)
        if not only_safety:
            ## try fairness refinement
            start = time.time()
            print("trying fairness refinement")
            success, result = try_liveness_refinement(mm,
                                                      program,
                                                      predicate_abstraction,
                                                      agreed_on_execution,
                                                      disagreed_on_state,
                                                      loop_counter,
                                                      allow_user_input)

            logging.info("liveness refinement took " + str(time.time() - start))
        else:
            success = False
            result = None

        if success:
            loop_counter = loop_counter + 1
            (new_state_preds, new_tran_preds), new_ltl_constraints = result

        if eager or (not success and result is None):
            ## do safety refinement
            start = time.time()
            print("trying safety refinement")
            success, result = safety_refinement_seq_int(program,
                                                predicate_abstraction,
                                                agreed_on_execution,
                                                disagreed_on_state,
                                                allow_user_input,
                                                keep_only_bool_interpolants,
                                                conservative_with_state_predicates)

            logging.info("safety refinement took " + str(time.time() - start))
            if success:
                new_state_preds = result
            else:
                raise Exception("Could not find any new state predicates.")


def write_counterexample(program,
                         agreed_on_transitions: [(Transition, dict)],
                         # disagreed_on_transitions: ([Transition], dict),
                         program_actually_took: [(Transition, dict)]):
    logging.info("Mismatch:")
    logging.info("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        logging.info("\nvar values: " + ", ".join(
            [str(v) + "=" + state[str(v)] for v in vs]))
        logging.info(("env: " if "env" == state["turn"] else "con: ") + str(trans))

    logging.info("Environment did not want to take:")

    logging.info(("env: " if "env" == program_actually_took[1]["turn"] else "con: ") + str(program_actually_took[0]))
    vs = []
    vs += set(program_actually_took[0].condition.variablesin()
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("mon_")]
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("pred_")]
              + [v for v in program.env_events + program.con_events])
    logging.info("with state: " + ", ".join([str(v) + "=" + program_actually_took[1][str(v)] for v in vs]))


def write_counterexample_state(program,
                               agreed_on_transitions: [(Transition, dict)],
                               disagreed_on_state: ([Formula], dict)):
    logging.info("Mismatch:")
    logging.info("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        logging.info("\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))
        logging.info(("env: " if "env" == state["turn"] else "con: ") + str(trans))

    logging.info("Environment wanted state to satisfy:")

    logging.info(", ".join([str(p) for p in disagreed_on_state[0]]))

    logging.info("Program however has state:")
    logging.info(", ".join([v + " = " + k for v, k in disagreed_on_state[1].items()]))
