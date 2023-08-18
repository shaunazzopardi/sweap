from typing import Tuple

from programs.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from programs.abstraction.interface.ltl_abstraction_types import LTLAbstractionStructureType, \
    LTLAbstractionTransitionType, LTLAbstractionBaseType
from programs.analysis.compatibility_checking.compatibility_checking import compatibility_checking
from programs.analysis.smt_checker import SMTChecker

from parsing.string_to_ltl import string_to_ltl
from programs.program import Program
from programs.refinement.fairness_refinement.ranking_refinement import try_liveness_refinement
from programs.refinement.safety_refinement.interpolation_refinement import safety_refinement
from programs.synthesis import ltl_synthesis
from programs.synthesis.ltl_synthesis import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from programs.synthesis.mealy_machine import MealyMachine
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import neg, G, F, implies, conjunct, disjunct, true, conjunct_formula_set
from prop_lang.variable import Variable

smt_checker = SMTChecker()


def synthesize(program: Program,
               ltl_text: str,
               tlsf_path: str,
               docker: bool,
               project_on_abstraction=False) -> Tuple[bool, Program]:
    # if not program.deterministic:
    #     raise Exception("We do not handle non-deterministic programs yet.")

    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if " Error\"" in ltl_text:
            raise Exception("Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text)
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)
    else:
        in_acts_syfco = []
        out_acts_syfco = []

    ltl = string_to_ltl(ltl_text)

    if isinstance(ltl, BiOp) and (ltl.op == "->" or ltl.op == "=>"):
        ltl_assumptions = ltl.left
        ltl_guarantees = ltl.right
    else:
        ltl_assumptions = true()
        ltl_guarantees = ltl

    in_acts = [e for e in program.env_events]
    out_acts = [e for e in program.con_events]
    prog_acts = program.out_events

    if tlsf_path is not None:
        if any(x for x in in_acts + prog_acts if x not in in_acts_syfco):
            raise Exception("TLSF file has different input variables than the program.")

        if any(x for x in out_acts if x not in out_acts_syfco):
            raise Exception("TLSF file has different output variables than the program.")

    return abstract_synthesis_loop(program, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker,
                                   project_on_abstraction=project_on_abstraction)


def abstract_synthesis_loop(program: Program, ltl_assumptions: Formula, ltl_guarantees: Formula, in_acts: [Variable],
                            out_acts: [Variable], docker: str, project_on_abstraction=False, debug=False) -> \
        Tuple[bool, MealyMachine]:
    eager = False
    keep_only_bool_interpolants = False
    use_explicit_loops_abstraction = False
    allow_user_input = False
    choose_predicates = False
    conservative_with_state_predicates = False
    prefer_lasso_counterexamples = False

    # TODO when we have a predicate mismatch we also need some information about the guard of the transition being taken
    #  by the program since some information about why the environment chose the wrong predicates is hidden there
    #  a solution here may be to use the atomic predicates appearing the in the transition guard as state predicates

    add_all_boolean_vars = True

    state_predicates = []
    transition_predicates = []
    ranking_invars = {}

    if add_all_boolean_vars:
        new_state_preds = [Variable(b.name) for b in program.valuation if b.type.lower().startswith("bool")]
    else:
        new_state_preds = []

    new_ranking_invars = {}

    new_transition_predicates = []

    transition_fairness = []
    predicate_abstraction = EffectsAbstraction(program)

    pred_acts = []
    state_pred_label_to_formula = {}
    symbol_table = predicate_abstraction.program.symbol_table
    symbol_table.update({tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation})

    base_type = LTLAbstractionBaseType.explicit
    transition_type = LTLAbstractionTransitionType.combined
    structure_type = LTLAbstractionStructureType.predicate_state

    mon_events = program.out_events \
                 + [Variable(s) for s in program.states]

    while True:
        for invars in new_ranking_invars.values():
            new_state_preds.extend(invars)

        state_predicates.extend(new_state_preds)
        transition_predicates.extend(new_transition_predicates)

        # symbol_table["inloop"] = TypedValuation("inloop", "bool", True)
        # symbol_table["notinloop"] = TypedValuation("notinloop", "bool", True)

        ## update predicate abstraction
        predicate_abstraction.add_predicates(new_state_preds, new_transition_predicates, True)
        ## LTL abstraction
        base_abstraction, ltl_abstraction = predicate_abstraction.to_ltl(base_type=base_type,
                                                                         transition_type=transition_type,
                                                                         structure_type=structure_type)
        print(", ".join(map(str, ltl_abstraction)))

        all_preds = state_predicates + transition_predicates
        all_new_preds = new_state_preds + new_transition_predicates
        new_state_preds.clear()

        new_pred_name_dict = {p: label_pred(p, all_preds) for p in all_new_preds}
        state_pred_label_to_formula.update(
            {label_pred(p, all_preds): p for p in all_new_preds})  # + transition_predicates_prev}
        state_pred_label_to_formula.update(
            {neg(label_pred(p, all_preds)): neg(p) for p in all_new_preds})  # + transition_predicates_prev}
        pred_acts.extend([new_pred_name_dict[v] for v in new_pred_name_dict.keys()])

        # should be computed incrementally
        i = 0
        while i < len(new_transition_predicates):
            dec = new_pred_name_dict[new_transition_predicates[i]]
            inc = new_pred_name_dict[new_transition_predicates[i + 1]]
            ranking = new_transition_predicates[i].right
            if debug:
                assert not any(v for v in ranking.variablesin() if "_prev" in v.name)

            invar_vars = [new_pred_name_dict[p] for p in new_ranking_invars[ranking]]
            invar_formula = conjunct_formula_set(invar_vars)

            transition_fairness.extend([
                implies(G(F(conjunct(invar_formula, dec))), G(F((disjunct(inc, neg(invar_formula)))))).simplify()])
            # transition_fairness += [implies(G(F(conjunct(invar_formula, disjunct(dec, dec_prev)))), G(F(disjunct(inc, inc_prev))))]
            i += 2

        new_transition_predicates.clear()
        new_ranking_invars.clear()

        symbol_table.update({
            str(label_pred(v, all_new_preds)): TypedValuation(str(label_pred(v, all_new_preds)), "bool", true()) for v
            in
            all_new_preds})

        assumptions = [ltl_assumptions] + transition_fairness + ltl_abstraction
        guarantees = [ltl_guarantees]

        (real, mm) = ltl_synthesis.ltl_synthesis(assumptions,
                                                 guarantees,
                                                 in_acts + mon_events + pred_acts,
                                                 out_acts,
                                                 docker)

        if real and not debug:
            print("Realizable")
            if project_on_abstraction:
                print(mm.to_dot(all_preds))
                return True, mm  # mm.project_controller_on_program((
                # "strategy" if real else "counterstrategy"),
                # program, predicate_abstraction.py,
                # symbol_table | symbol_table_preds)
            else:
                # mm = mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(predicate_abstraction.py, program)
                return True, mm  # mm.to_dot(pred_list)

        print(mm.to_dot(all_preds))

        if base_type == LTLAbstractionBaseType.explicit and \
                transition_type == LTLAbstractionTransitionType.combined and \
                structure_type == LTLAbstractionStructureType.predicate_state:
            mm = mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(predicate_abstraction,
                                                                                           program,
                                                                                           base_abstraction)
            print("Mealy Machine with filled in controller steps:\n" + str(mm.to_dot(all_preds)))

        ## compatibility checking
        determination, result = compatibility_checking(program,
                                                       predicate_abstraction,
                                                       mm,
                                                       real,
                                                       mon_events,
                                                       all_preds,
                                                       symbol_table,
                                                       state_pred_label_to_formula,
                                                       project_on_abstraction,
                                                       prefer_lasso_counterexamples)

        if determination == False:
            print("Problem is unrealisable.")
            return False, mm
        elif determination == True:
            raise Exception("error")
        else:
            ce, agreed_on_transitions, disagreed_on_state, counterstrategy_states = result

        write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)

        ## try fairness refinement
        success, result = try_liveness_refinement(counterstrategy_states,
                                                  program,
                                                  predicate_abstraction,
                                                  agreed_on_transitions,
                                                  disagreed_on_state,
                                                  symbol_table,
                                                  state_pred_label_to_formula,
                                                  ranking_invars,
                                                  allow_user_input)

        if success:
            new_ranking_invars, new_transition_predicates = result

        ## do safety refinement
        if eager or not success:
            success, result = safety_refinement(program,
                                                predicate_abstraction,
                                                agreed_on_transitions,
                                                disagreed_on_state,
                                                ce,
                                                symbol_table,
                                                allow_user_input,
                                                keep_only_bool_interpolants,
                                                conservative_with_state_predicates)

            if success:
                new_state_preds = result
            else:
                raise Exception("Could not find any new state predicates.")


def write_counterexample(program,
                         agreed_on_transitions: [(Transition, dict)],
                         # disagreed_on_transitions: ([Transition], dict),
                         program_actually_took: [(Transition, dict)]):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(("env: " if "env" == state["turn"] else "con: ") + str(trans) + "\nvar values: " + ", ".join(
            [str(v) + "=" + state[str(v)] for v in vs]) + "\n")

    # print("Environment wanted to take one of these:")

    # state = disagreed_on_transitions[1]
    # vs = []
    # for trans in disagreed_on_transitions[0]:
    #     vs += set(trans.condition.variablesin()
    #               + [v for v in list(state.keys()) if str(v).startswith("mon_")]
    #               + [v for v in list(state.keys()) if str(v).startswith("pred_")]
    #               + [v for v in program.env_events + program.con_events])
    #     print(str(trans))
    # print("with state: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))
    #
    # print("Program actually took:")
    print("Environment did not want to take:")

    print(("env: " if "env" == program_actually_took[1]["turn"] else "con: ") + str(program_actually_took[0]))
    vs = []
    vs += set(program_actually_took[0].condition.variablesin()
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("mon_")]
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("pred_")]
              + [v for v in program.env_events + program.con_events])
    print("with state: " + ", ".join([str(v) + "=" + program_actually_took[1][str(v)] for v in vs]))


def write_counterexample_state(program,
                               agreed_on_transitions: [(Transition, dict)],
                               disagreed_on_state: ([Formula], dict)):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(("env: " if "env" == state["turn"] else "con: ") + str(trans) + "\nvar values: " + ", ".join(
            [str(v) + "=" + state[str(v)] for v in vs]) + "\n")

    print("Environment wanted state to satisfy:")

    print(", ".join([str(p) for p in disagreed_on_state[0]]))

    print("Program however has state:")
    print(", ".join([v + " = " + k for v, k in disagreed_on_state[1].items()]))
