from programs.abstraction.explicit_abstraction.util.abstract_state import AbstractState
from programs.program import Program
from programs.transition import Transition
from programs.util import transition_formula, safe_update_set_vals, stringify_pred_take_out_neg, powerset, \
    safe_update_list_vals, stringify_pred
from prop_lang.util import conjunct_formula_set, neg, sat


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
    # old_tate_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
    # old_state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

    # for t in env_transitions:
    #     if t not in predAbs.env_to_program_transitions.keys():
    #         print()
    # for t in con_transitions:
    #     if t not in predAbs.con_to_program_transitions.keys():
    #         print()

    for t in new_env_to_program_transitions.keys():
        if t.tgt not in predAbs.state_to_con_transitions.keys():
            print()
    for t in new_con_to_program_transitions.keys():
        if t.tgt not in predAbs.state_to_env_transitions.keys():
            print()


    # predAbs.state_to_env_transitions = {}
    # for t in env_transitions:
    #     safe_update_list_vals(predAbs.state_to_env_transitions, t.src, [t])
    # predAbs.state_to_con_transitions = {}
    # for t in con_transitions:
    #     safe_update_list_vals(predAbs.state_to_con_transitions, t.src, [t])

    program = predAbs.get_program()
    #
    # # TODO, after this can reduce abstract_effects
    # keep_env = set()
    # keep_con = set()
    # new_state_to_env = {}
    # new_state_to_con = {}
    #
    # env_done_states = set()
    # con_done_states = set()
    # next_states = {init_st}
    # env_turn = True
    # prog_state_to_preconditions = {s:set() for s in predAbs.program.states}
    # while len(next_states) > 0:
    #     new_next = set()
    #     for st in next_states:
    #         if env_turn:
    #             env_done_states.add(st)
    #             if st not in predAbs.state_to_env_transitions.keys():
    #                 print()
    #             current_trans = predAbs.state_to_env_transitions[st]
    #             new_state_to_env[st] = predAbs.state_to_env_transitions[st]
    #             keep_env.update(current_trans)
    #             if st != init_st:
    #                 prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
    #             for t in current_trans:
    #                 if t.tgt not in con_done_states:
    #                     new_next.add(t.tgt)
    #         else:
    #             prog_state_to_preconditions[st.state].add(frozenset(st.predicates))
    #             con_done_states.add(st)
    #             current_trans = predAbs.state_to_con_transitions[st]
    #             new_state_to_con[st] = predAbs.state_to_con_transitions[st]
    #             keep_con.update(current_trans)
    #             for t in current_trans:
    #                 if t.tgt not in env_done_states:
    #                     new_next.add(t.tgt)
    #     next_states = new_next
    #     env_turn = not env_turn
    #
    # env_transitions = list(keep_env)
    # con_transitions = list(keep_con)
    #
    # all_prog_trans = predAbs.abstract_effect.keys()
    # for t in all_prog_trans:
    #     all_preconditions = prog_state_to_preconditions[t.src]
    #     all_items = set(predAbs.abstract_effect[t].items())
    #     for E, effects in all_items:
    #         effects.keep_only_values(all_preconditions)
    #         if len(effects) == 0:
    #             del predAbs.abstract_effect[t][E]

    # predAbs.state_to_env_transitions = new_state_to_env
    # predAbs.state_to_con_transitions = new_state_to_con
    predAbs.pretty_print_abstract_effect()

    one_step_abstraction = Program("pred_abst_" + program.name, states | {init_st},
                                   init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events + [stringify_pred(t) for t in predAbs.get_transition_predicates()],
                                   False, preprocess=False)
    predAbs.abstraction = one_step_abstraction
    return one_step_abstraction