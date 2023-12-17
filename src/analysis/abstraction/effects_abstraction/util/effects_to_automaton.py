from analysis.abstraction.explicit_abstraction.util.abstract_state import AbstractState
from programs.program import Program
from programs.transition import Transition
from programs.util import transition_formula, safe_update_set_vals, powerset, \
    safe_update_list_vals
from prop_lang.util import conjunct_formula_set, neg, sat, stringify_pred, stringify_pred_take_out_neg


def effects_to_explicit_automaton_abstraction(predAbs):
    states = set()
    env_transitions = []
    new_env_to_program_transitions = {}
    predAbs.state_to_env_transitions = {}
    predAbs.state_to_con_transitions = {}

    init_st = predAbs.get_program().initial_state
    states.add(init_st)
    for t in predAbs.init_program_trans:
        t_f = transition_formula(t)

        for _, E in predAbs.abstract_guard_env_disjuncts[t]:
            next = set()

            for p in predAbs.get_state_predicates():
                if sat(conjunct_formula_set(E | {p, t_f}), predAbs.get_program().symbol_table):
                    next.add(p)
                else:
                    next.add(neg(p))

            tran_preds = []
            for p in predAbs.get_transition_predicates():
                if sat(conjunct_formula_set(E | {p, t_f}), predAbs.get_program().symbol_table):
                    tran_preds.append(p)
                else:
                    tran_preds.append(neg(p))

            tgt = AbstractState(t.tgt, next)
            states.add(tgt)
            abs_trans = Transition(init_st,
                                   conjunct_formula_set(E),
                                   [],
                                   t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                   tgt).complete_outputs(predAbs.get_program().out_events)
            safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
            safe_update_set_vals(predAbs.state_to_env_transitions, init_st, {abs_trans})
            # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
            env_transitions.append(abs_trans)

    #TODO should do this only for every transition formula
    #TODO parallelize?
    for t in predAbs.abstract_guard_env.keys():
        if t in predAbs.init_program_trans:
            continue
        t_f = transition_formula(t)
        for E, effects in predAbs.abstract_effect[t].items():
            for nextPs, Ps in effects.items():
                nextPs_without_tran_preds = set()
                tran_preds = []
                for p in nextPs:
                    if any(v for v in p.variablesin() if "_prev" in str(v)):
                        tran_preds.append(p)
                    else:
                        nextPs_without_tran_preds.add(p)
                nextPs_with_constants = set()
                for p in predAbs.abstract_effect_constant[t]:
                    if any(v for v in p.variablesin() if "_prev" in str(v)):
                        tran_preds.append(p)
                    else:
                        nextPs_with_constants.add(p)
                tran_preds.extend(predAbs.abstract_effect_tran_preds_constant[t])
                nextPs_with_constants.update(set(nextPs_without_tran_preds))
                for P in Ps:
                    invars = set()
                    unused_invars = set()
                    for p in predAbs.abstract_effect_invars[t]:
                        if p in P:
                            invars.add(p)
                        elif neg(p) in P:
                            invars.add(neg(p))
                        else:
                            unused_invars.add(p)
                    if len(unused_invars) > 0:
                        for p_set in powerset(unused_invars):
                            p_set_closed_src = p_set | P
                            p_set_closed_src = p_set_closed_src | {neg(p) for p in predAbs.get_state_predicates() if p not in p_set_closed_src and neg(p) not in p_set_closed_src}
                            p_set_closed_tgt = p_set | nextPs_with_constants | invars
                            p_set_closed_tgt |= {neg(p) for p in predAbs.get_state_predicates() if p not in p_set_closed_tgt and neg(p) not in p_set_closed_tgt}
                            tgt = AbstractState(t.tgt, p_set_closed_tgt)
                            src = AbstractState(t.src, P.union(p_set_closed_src))
                            states.add(src)
                            states.add(tgt)
                            abs_trans = Transition(src,
                                                  conjunct_formula_set(E),
                                                  [],
                                                  t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                                  tgt).complete_outputs(predAbs.get_program().out_events)
                            safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                            safe_update_set_vals(predAbs.state_to_env_transitions, src, {abs_trans})
                    else:
                        tgt = AbstractState(t.tgt, invars.union(nextPs_with_constants))
                        src = AbstractState(t.src, P)
                        states.add(src)
                        states.add(tgt)
                        abs_trans = Transition(src,
                                               conjunct_formula_set(E),
                                               [],
                                               t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                               tgt).complete_outputs(predAbs.get_program().out_events)
                        safe_update_set_vals(new_env_to_program_transitions, abs_trans, {t})
                        safe_update_set_vals(predAbs.state_to_env_transitions, src, {abs_trans})

                    # safe_update_set_vals(new_program_env_to_abstract_env_transitions, t, {abs_trans})
                    # env_transitions.append(abs_trans)

    con_transitions = []
    new_con_to_program_transitions = {}
    for t in predAbs.abstract_guard_con.keys():
        t_f = transition_formula(t)
        for E, effects in predAbs.abstract_effect[t].items():
            for nextPs, Ps in effects.items():
                nextPs_without_tran_preds = set()
                tran_preds = []
                for p in nextPs:
                    if any(v for v in p.variablesin() if "_prev" in str(v)):
                        tran_preds.append(p)
                    else:
                        nextPs_without_tran_preds.add(p)
                nextPs_with_constants = set()
                for p in predAbs.abstract_effect_constant[t]:
                    if any(v for v in p.variablesin() if "_prev" in str(v)):
                        tran_preds.append(p)
                    else:
                        nextPs_with_constants.add(p)
                tran_preds.extend(predAbs.abstract_effect_tran_preds_constant[t])
                nextPs_with_constants.update(set(nextPs_without_tran_preds))
                for P in Ps:
                    invars = set()
                    unused_invars = set()
                    for p in predAbs.abstract_effect_invars[t]:
                        if p in P:
                            invars.add(p)
                        elif neg(p) in P:
                            invars.add(neg(p))
                        else:
                            unused_invars.add(p)
                    if len(unused_invars) > 0:
                        for p_set in powerset(unused_invars):
                            p_set_closed_src = p_set | P
                            p_set_closed_src = p_set_closed_src | {neg(p) for p in predAbs.get_state_predicates() if p not in p_set_closed_src and neg(p) not in p_set_closed_src}
                            p_set_closed_tgt = p_set | nextPs_with_constants | invars
                            p_set_closed_tgt |= {neg(p) for p in predAbs.get_state_predicates() if p not in p_set_closed_tgt and neg(p) not in p_set_closed_tgt}
                            tgt = AbstractState(t.tgt, p_set_closed_tgt)
                            src = AbstractState(t.src, P.union(p_set_closed_src))
                            states.add(src)
                            states.add(tgt)
                            abs_trans = Transition(src,
                                                  conjunct_formula_set(E),
                                                  [],
                                                  t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                                  tgt).complete_outputs(predAbs.get_program().out_events)
                            safe_update_set_vals(new_con_to_program_transitions, abs_trans, {t})
                            safe_update_set_vals(predAbs.state_to_con_transitions, src, {abs_trans})
                            # safe_update_set_vals(new_program_con_to_abstract_con_transitions, t, {abs_trans})
                            # con_transitions.append(abs_trans)
                    else:
                        tgt = AbstractState(t.tgt, invars.union(nextPs_with_constants))
                        src = AbstractState(t.src, P)
                        states.add(src)
                        states.add(tgt)
                        abs_trans = Transition(src,
                                               conjunct_formula_set(E),
                                               [],
                                               t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                               tgt).complete_outputs(predAbs.get_program().out_events)
                        safe_update_set_vals(new_con_to_program_transitions, abs_trans, {t})
                        safe_update_set_vals(predAbs.state_to_con_transitions, src, {abs_trans})

    predAbs.env_to_program_transitions = new_env_to_program_transitions
    predAbs.con_to_program_transitions = new_con_to_program_transitions
    env_transitions = new_env_to_program_transitions.keys()
    con_transitions = new_con_to_program_transitions.keys()

    predAbs.state_to_env_transitions = {}
    predAbs.state_to_con_transitions = {}
    for t in env_transitions:
        safe_update_list_vals(predAbs.state_to_env_transitions, t.src, [t])
    for t in con_transitions:
        safe_update_list_vals(predAbs.state_to_con_transitions, t.src, [t])

    for s in states:
        # TODO this is important for some reason
        #      sometimes that are con_transitions that go to an state with no outgoing env transitions (and vice-versa)
        #      this may indicate a bug in the abstraction algorithm,
        if s not in predAbs.state_to_env_transitions.keys():
            predAbs.state_to_env_transitions[s] = []
        if s not in predAbs.state_to_con_transitions.keys():
            predAbs.state_to_con_transitions[s] = []

    program = predAbs.get_program()

    predAbs.pretty_print_abstract_effect()

    one_step_abstraction = Program("pred_abst_" + program.name, states | {init_st},
                                   init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events + [stringify_pred(t) for t in predAbs.get_transition_predicates()],
                                   False, preprocess=False)
    predAbs.abstraction = one_step_abstraction
    return one_step_abstraction