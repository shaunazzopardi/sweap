from pysmt.shortcuts import And

from programs.abstraction.interface.predicate_abstraction import PredicateAbstraction
from programs.analysis.smt_checker import SMTChecker
from programs.util import looping_to_normal, stutter_transition, preds_in_state, var_to_predicate, is_predicate_var
from prop_lang.util import neg, conjunct_formula_set, disjunct_formula_set, propagate_negations
from prop_lang.variable import Variable


def concretize_transitions(program,
                           looping_program,
                           predicate_abstraction: PredicateAbstraction,
                           indices_and_state_list,
                           incompatible_state):
    transitions = looping_program.env_transitions + looping_program.con_transitions
    smt_checker = SMTChecker()

    # ignore the mismatch state
    new_indices_and_state_list = indices_and_state_list
    concretized = []
    for (i, st) in new_indices_and_state_list:
        if int(i) != -1:
            concretized += [(looping_to_normal(transitions[int(i)]), st)]
        else:
            stutter_trans = stutter_transition(program, [q for q in program.states if st[str(q)] == "TRUE"][0],
                                               st["turn"] == "env")
            if stutter_trans == None:
                raise Exception("stuttering transition not found")
            else:
                concretized += [(stutter_trans, st)]

    # two options, either we stopped because of a predicate mismatch, or a transition mismatch
    incompatibility_formula = []
    if incompatible_state["compatible_states"] == "FALSE" or incompatible_state["compatible_outputs"] == "FALSE":
        if program.deterministic:
            return concretized[:-1], ([neg(concretized[-1][0].condition)], concretized[-1][1]), concretized[-1]
        else:
            # if program is not deterministic, we need to identify the transitions the counterstrategy wanted to take rather than the one the program actually took
            try:
                state_before_mismatch = concretized[-2][1]
            except Exception as e:
                raise e
            src_state = concretized[-2][0].tgt
            tgt_state_env_wanted = [p for p in program.states if incompatible_state["mon_" + str(p)] == "TRUE"][0]
            outputs_env_wanted = [p for p in program.out_events if incompatible_state["mon_" + str(p)] == "TRUE"]
            outputs_env_wanted += [neg(p) for p in program.out_events if incompatible_state["mon_" + str(p)] == "FALSE"]
            if incompatible_state["turn"] == "mon_env":
                candidate_transitions = [t for t in program.env_transitions if
                                         t.src == src_state and t.tgt == tgt_state_env_wanted and set(t.output) == set(
                                             outputs_env_wanted)]
                if tgt_state_env_wanted == src_state:
                    stutter = stutter_transition(program, src_state, True)
                    if stutter is not None:
                        candidate_transitions.append(stutter)
            elif incompatible_state["turn"] == "mon_con":
                candidate_transitions = [t for t in program.con_transitions if
                                         t.src == src_state and t.tgt == tgt_state_env_wanted and set(t.output) == set(
                                             outputs_env_wanted)]
                if tgt_state_env_wanted == src_state:
                    stutter = stutter_transition(program, src_state, False)
                    if stutter is not None:
                        candidate_transitions.append(stutter)
            else:
                raise Exception("Mismatches should only occur at mon_env or mon_con turns")

            compatible_with_abstract_state = []
            for str_p in state_before_mismatch.keys():
                if is_predicate_var(str_p):
                    p = Variable(str_p)
                    if state_before_mismatch[str_p] == "TRUE":
                        compatible_with_abstract_state += [var_to_predicate(p)]
                    else:
                        compatible_with_abstract_state += [neg(var_to_predicate(p))]

            abstract_state = conjunct_formula_set(compatible_with_abstract_state)
            env_desired_transitions = [t for t in candidate_transitions
                                       if smt_checker.check(And(*abstract_state.to_smt(program.symbol_table),
                                                                *t.condition.to_smt(program.symbol_table)))]
            formula = disjunct_formula_set([t.condition for t in env_desired_transitions] + [
                propagate_negations(neg(concretized[-1][0].condition))])
            return concretized[:-1], ([formula], concretized[-1][1]), concretized[-1]
    else:
        env_pred_state = None
        if incompatible_state["compatible_state_predicates"] == "FALSE" or incompatible_state[
            "compatible_tran_predicates"] == "FALSE":
            # pred mismatch
            incompatibility_formula += preds_in_state(incompatible_state)
            #TODO we wanted to take the wrong transition, but the condition at state concretized[-1][1], not at incompatible_state
            # incompatibility_formula += [neg(concretized[-1][0].condition)]
            env_pred_state = (incompatibility_formula, incompatible_state)

        return concretized, env_pred_state, concretized[-1]

