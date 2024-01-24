import logging
import time
from typing import Tuple

from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from analysis.abstraction.interface.ltl_abstraction_type import LTLAbstractionStructureType, \
    LTLAbstractionTransitionType, LTLAbstractionBaseType, LTLAbstractionType, LTLAbstractionOutputType
from analysis.compatibility_checking.compatibility_checking import compatibility_checking
from analysis.refinement.fairness_refinement.ranking_refinement import ranking_refinement

from parsing.string_to_ltl import string_to_ltl
from programs.program import Program
from analysis.refinement.fairness_refinement.fairness_util import try_liveness_refinement
from analysis.refinement.safety_refinement.interpolation_refinement import safety_refinement_seq_int
from prop_lang.mathexpr import MathExpr
from prop_lang.value import Value
from synthesis.ltl_synthesis import ltl_synthesis, syfco_ltl, syfco_ltl_in, syfco_ltl_out
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from synthesis.mealy_machine import MealyMachine
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import true, stringify_formula, should_be_math_expr, normalise_mathexpr, atomic_predicates, \
    is_tautology
from prop_lang.variable import Variable

import analysis.abstraction.effects_abstraction.effects_to_ltl as effects_to_ltl


def synthesize(program: Program,
               ltl: Formula,
               tlsf_path: str,
               docker: bool,
               project_on_abstraction=False) -> Tuple[bool, MealyMachine]:
    # if not program.deterministic:
    #     raise Exception("We do not handle non-deterministic programs yet.")

    start = time.time()
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

    result = abstract_synthesis_loop(program, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker,
                                     project_on_abstraction=project_on_abstraction)
    logging.info("synthesis took " + str(time.time() - start))
    return result


def abstract_synthesis_loop(program: Program, ltl_assumptions: [Formula], ltl_guarantees: [Formula], in_acts: [Variable],
                            out_acts: [Variable], docker: bool, project_on_abstraction=False, debug=False) -> \
        Tuple[bool, MealyMachine]:
    eager = False
    keep_only_bool_interpolants = False
    use_explicit_loops_abstraction = False
    allow_user_input = False
    choose_predicates = False
    conservative_with_state_predicates = False
    prefer_lasso_counterexamples = True
    add_tran_preds_immediately = False
    add_tran_preds_after_state_abstraction = True

    # TODO when we have a predicate mismatch we also need some information about the guard of the transition being taken
    #  by the program since some information about why the environment chose the wrong predicates is hidden there
    #  a solution here may be to use the atomic predicates appearing the in the transition guard as state predicates

    add_all_boolean_vars = True

    if add_all_boolean_vars:
        new_state_preds = [Variable(b.name) for b in program.valuation if b.type.lower().startswith("bool")]
    else:
        new_state_preds = []

    # for t in program.transitions:
    #     preds_in_cond = atomic_predicates(t.condition)
    #     new_state_preds.extend([p for p in preds_in_cond if p not in program.con_events + program.env_events])

    new_ltl_assumptions = []
    for ltl in ltl_assumptions:
        new_ltl, preds = stringify_formula(ltl, in_acts + out_acts)
        new_state_preds += preds
        new_ltl_assumptions.append(new_ltl)

    new_ltl_guarantees = []
    for ltl in ltl_guarantees:
        new_ltl, preds = stringify_formula(ltl, in_acts + out_acts)
        new_state_preds += preds
        new_ltl_guarantees.append(new_ltl)

    ltl_assumptions = new_ltl_assumptions
    ltl_guarantees = new_ltl_guarantees

    new_state_preds = list(set(new_state_preds))

    new_tran_preds = set()
    new_ltl_constraints = set()

    # for tv in program.valuation:
    #     if tv.type.lower().startswith("bool"):
    #         continue
    #     if tv.type.lower().startswith("int"):
    #         ranking_bot = Variable(tv.name)
    #         invars_bot = [BiOp(ranking_bot, ">=", 0)]
    #         rankings += [ranking_refinement(ranking_bot, invars_bot)]
    #
    #         ranking_top = BiOp(Value("1"), "-", Variable(tv.name))
    #         invars_top = [BiOp(ranking_top, ">=", 0)]
    #         rankings += [ranking_refinement(ranking_top, invars_top)]
    #     elif tv.type.lower().startswith("nat"):
    #         ranking = Variable(tv.name)
    #         invars = []
    #         rankings += [ranking_refinement(ranking, invars)]
    #     elif ".." in tv.type:
    #         ranking_bot = Variable(tv.name)
    #         invars_bot = []
    #         rankings += [ranking_refinement(ranking_bot, invars_bot)]
    #
    #         ranking_top = BiOp(Value("1"), "-", Variable(tv.name))
    #         invars_top = []
    #         rankings += [ranking_refinement(ranking_top, invars_top)]


    loop_counter = 0

    ltlAbstractionType: LTLAbstractionType = LTLAbstractionType(LTLAbstractionBaseType.effects_representation,
                                                                LTLAbstractionTransitionType.one_trans,
                                                                LTLAbstractionStructureType.control_state,
                                                                LTLAbstractionOutputType.no_output)


    predicate_abstraction = EffectsAbstraction(program)

    mon_events = program.out_events \
                 + [Variable(s) for s in program.states]

    original_LTL_problem = LTLSynthesisProblem(in_acts,
                                               out_acts,
                                               ltl_assumptions,
                                               ltl_guarantees)

    # # see if solvable immediately when turning to boolean problem
    # start = time.time()
    # base_abstraction, abstract_ltl_problem = effects_to_ltl.to_ltl(predicate_abstraction,
    #                                                                original_LTL_problem,
    #                                                                ltlAbstractionType)
    #
    #
    # print("running LTL synthesis")
    # (real, mm_hoa) = ltl_synthesis(abstract_ltl_problem)
    #
    # if real and not debug:
    #     logging.info("Realizable")
    #     if project_on_abstraction:
    #         # TODO actually project
    #         print("massaging abstract controller")
    #         mm = predicate_abstraction.massage_mealy_machine(mm_hoa,
    #                                                          base_abstraction,
    #                                                          ltlAbstractionType,
    #                                                          abstract_ltl_problem,
    #                                                          real)
    #         return True, mm
    #     else:
    #         return True, mm_hoa


    timing_data = ""
    print("Starting abstract synthesis loop.")

    while True:
        if add_tran_preds_immediately:
            rankings = []
            for state_pred in new_state_preds + predicate_abstraction.state_predicates:
                if isinstance(state_pred, MathExpr) or should_be_math_expr(state_pred):
                    fs = normalise_mathexpr(state_pred)
                    for f in fs:
                        invar = []
                        if not is_tautology(f, program.symbol_table):
                            invar.append(f)

                        rankings.append(ranking_refinement(f.right, (invar)))

            for atoms, constraints in rankings:
                for atom in atoms:
                    if any(v for v in atom.variablesin() if "_prev" in str(v)):
                        new_tran_preds.append(atom)
                    else:
                        new_state_preds.append(atom)
                new_ltl_constraints.update(constraints)
            add_tran_preds_after_state_abstraction = False
            add_tran_preds_immediately = False

        new_state_preds = [p for p in set(new_state_preds) if p not in predicate_abstraction.state_predicates]
        new_tran_preds = [p for p in set(new_tran_preds) if p not in predicate_abstraction.transition_predicates]
        # new_state_preds = list(map(string_to_prop, ["(cnt < 2)", "(cnt <= 0)", "(cnt >= 0)", "(cnt >= 2)"]))
        # new_state_preds = list(map(string_to_prop, ["(cnt >= 0)", "(cnt < 2)", "(cnt >= 2)", "(cnt <= 0)"]))
        ## update predicate abstraction
        start = time.time()
        print("adding " + ", ".join(map(str, new_state_preds + new_tran_preds)) + " to predicate abstraction")
        predicate_abstraction.add_predicates(new_state_preds, new_tran_preds, True)
        timing_data += "\n" + ("adding " + ", ".join(map(str, (new_state_preds + new_tran_preds))) + " to predicate abstraction" + " took " + str(time.time() - start))
        print ("adding " + ", ".join(map(str, (new_state_preds + new_tran_preds))) + " to predicate abstraction" + " took " + str(time.time() - start))
        logging.info(timing_data)

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

        timing_data += "\n" + ("to ltl abstraction took " + str(time.time() - start))
        logging.info(timing_data)

        start = time.time()
        print("running LTL synthesis")
        (real, mm_hoa) = ltl_synthesis(abstract_ltl_problem)
        timing_data += "\n" + ("ltl synthesis took " + str(time.time() - start))
        logging.info(timing_data)

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
            continue

        start = time.time()
        print("massaging abstract counterstrategy")
        mm = predicate_abstraction.massage_mealy_machine(mm_hoa,
                                                         base_abstraction,
                                                         ltlAbstractionType,
                                                         abstract_ltl_problem,
                                                         real)

        timing_data += "\n" + ("massaging mealy machine took " + str(time.time() - start))
        logging.info(mm)
        logging.info(timing_data)
        print(mm.to_dot())

        ## compatibility checking
        start = time.time()

        print("checking for compatibility of counterstrategy with program")
        determination, result = compatibility_checking(program,
                                                       predicate_abstraction,
                                                       mm,
                                                       real,
                                                       base_abstraction,
                                                       ltlAbstractionType,
                                                       mon_events,
                                                       project_on_abstraction,
                                                       prefer_lasso_counterexamples)

        timing_data += "\n" + ("compatibility checking took " + str(time.time() - start))
        logging.info(timing_data)

        if determination == False:
            logging.info("Problem is unrealisable.")
            return False, mm
        elif determination == True:
            raise Exception("error")
        else:
            agreed_on_execution, disagreed_on_state = result

        # write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)

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

        timing_data += "\n" + ("liveness refinement took " + str(time.time() - start))
        logging.info(timing_data)

        if success:
            loop_counter = loop_counter + 1
            new_preds, new_ltl_constraints = result
            new_state_preds = {p for p in new_preds if not any (v for v in p.variablesin() if v not in program.local_vars or "_prev" in str(v))}
            new_tran_preds = {p for p in new_preds if any(v for v in p.variablesin() if "_prev" in str(v))}

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

            timing_data += "\n" + ("safety refinement took " + str(time.time() - start))
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
