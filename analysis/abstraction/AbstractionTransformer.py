from analysis.abstraction.explicit_abstraction.util.abstract_state import AbstractState
from programs.abstraction.predicate_abstraction_new import bookkeep_tran_preds
from programs.abstraction.predicate_abstraction_tran import powerset
from programs.program import Program
from programs.transition import Transition
from programs.util import transition_formula, stringify_pred_take_out_neg, safe_update_set_vals, safe_update_list_vals, \
    stringify_pred, label_preds, label_pred
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import neg, conjunct_formula_set, conjunct, disjunct_formula_set, X, \
    implies, G, sat, iff
from prop_lang.value import Value
from prop_lang.variable import Variable


def to_automaton_one_step(predAbs):
    # TODO this procedure is encoding every possible abstract transition
    #      but, with invars we are able to encode multiple transitions with one
    #      when the invar predicate is not relevant to the actions

    states = set()
    env_transitions = []
    new_env_to_program_transitions = {}
    predAbs.state_to_env_transitions = {}
    predAbs.state_to_con_transitions = {}

    init_st = predAbs.get_program.initial_state
    states.add(init_st)
    for t in predAbs.init_program_trans:
        t_f = transition_formula(t)

        for _, E in predAbs.abstract_guard_env_disjuncts[t]:
            next = set()

            for p in predAbs.get_state_predicates:
                if sat(conjunct_formula_set(E | {p, t_f}), predAbs.get_program.symbol_table):
                    next.add(p)
                else:
                    next.add(neg(p))

            tran_preds = []
            for p in predAbs.get_transition_predicates:
                if sat(conjunct_formula_set(E | {p, t_f}), predAbs.get_program.symbol_table):
                    tran_preds.append(p)
                else:
                    tran_preds.append(neg(p))

            tgt = AbstractState(t.tgt, next)
            states.add(tgt)
            abs_trans = Transition(init_st,
                                   conjunct_formula_set(E),
                                   [],
                                   t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                   tgt).complete_outputs(predAbs.get_program.out_events)
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
                tran_preds.extend(predAbs.abstract_effect_tran_preds_constant[t_f])
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
                            p_set_closed_src = p_set_closed_src | {neg(p) for p in predAbs.get_state_predicates if p not in p_set_closed_src and neg(p) not in p_set_closed_src}
                            p_set_closed_tgt = p_set | nextPs_with_constants | invars
                            p_set_closed_tgt |= {neg(p) for p in predAbs.get_state_predicates if p not in p_set_closed_tgt and neg(p) not in p_set_closed_tgt}
                            tgt = AbstractState(t.tgt, p_set_closed_tgt)
                            src = AbstractState(t.src, P.union(p_set_closed_src))
                            states.add(src)
                            states.add(tgt)
                            abs_trans = Transition(src,
                                                  conjunct_formula_set(E),
                                                  [],
                                                  t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                                  tgt).complete_outputs(predAbs.get_program.out_events)
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
                                               tgt).complete_outputs(predAbs.get_program.out_events)
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
                tran_preds.extend(predAbs.abstract_effect_tran_preds_constant[t_f])
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
                            p_set_closed_src = p_set_closed_src | {neg(p) for p in predAbs.get_state_predicates if p not in p_set_closed_src and neg(p) not in p_set_closed_src}
                            p_set_closed_tgt = p_set | nextPs_with_constants | invars
                            p_set_closed_tgt |= {neg(p) for p in predAbs.get_state_predicates if p not in p_set_closed_tgt and neg(p) not in p_set_closed_tgt}
                            tgt = AbstractState(t.tgt, p_set_closed_tgt)
                            src = AbstractState(t.src, P.union(p_set_closed_src))
                            states.add(src)
                            states.add(tgt)
                            abs_trans = Transition(src,
                                                  conjunct_formula_set(E),
                                                  [],
                                                  t.output + [stringify_pred_take_out_neg(t) for t in tran_preds],
                                                  tgt).complete_outputs(predAbs.get_program.out_events)
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
                                               tgt).complete_outputs(predAbs.get_program.out_events)
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

    program = predAbs.get_program
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
                                   program.con_events, program.out_events + [stringify_pred(t) for t in predAbs.get_transition_predicates],
                                   False, preprocess=False)
    predAbs.abstraction = one_step_abstraction
    return one_step_abstraction

def one_step_abstraction_to_hoa(predAbs, street_conditions):
    init_states, states, state_to_transitions = one_step_abstraction_to_combined_transition(predAbs)

    hoa = ["HOA: v1"]
    hoa += ["name: \"abstraction of " + predAbs.get_program.name + "\""]
    AP = predAbs.get_program.env_events + predAbs.get_program.con_events + predAbs.get_program.out_events + predAbs.get_state_predicates + predAbs.get_transition_predicates
    hoa += ["AP: " + str(len(AP)) + " " + " ".join("\"" + str(ap) + "\"" for ap in AP)]
    states = list(states)
    for st in init_states:
        hoa += ["Start: " + str(states.index(st))]
    hoa += ["States: " + str(len(states))]

    acc_cond = []
    cnt = 0
    tran_pred_to_acc_state = {}
    for fin, inf in street_conditions:
        acc_cond += ["Fin(" + str(cnt) + ")|Inf(" + str(cnt + 1) + ")"]
        tran_pred_to_acc_state[fin] = cnt
        tran_pred_to_acc_state[inf] = cnt + 1
        cnt += 2

    hoa += ["Acceptance: " + str(len(street_conditions)*2) + "&".join(acc_cond)]
    hoa += ["acc-name: Streett " + str(len(street_conditions))]
    hoa += ["--BODY--"]

    number_aps = [BiOp(Variable(str(ap)), ":=", Variable(str(i))) for i, ap in enumerate(AP)]

    for i, st in enumerate(states):
        transition_hoa = ["State: " + str(i)]
        if st not in state_to_transitions.keys():
            raise Exception("State " + str(st) + " not in state_to_transitions")
        for t in state_to_transitions[st]:
            # TODO write numbers instead of names in condition
            condition = conjunct_formula_set([t.condition] + t.output + t.tgt.predicates).replace(number_aps)
            if isinstance(condition, Value) and condition.is_true():
                condition = "t"
            elif isinstance(condition, Value) and condition.is_false():
                condition = "f"
            else:
                condition = str(condition)
            t_hoa = "[" + (condition) + "] " \
                               + str(states.index(t.tgt))
            acc_sets = []
            for o in t.output:
                if o in tran_pred_to_acc_state.keys():
                    acc_sets.append(tran_pred_to_acc_state[o])
            if len(acc_sets) > 0:
                t_hoa += " {" + ",".join(str(a) for a in acc_sets) + "}"
            transition_hoa.append(t_hoa)
        hoa += transition_hoa

    hoa += ["--END--"]

    return "\n".join(hoa)


# #structure: G(Q -> Ps -> Cs -> (V Es' & Q' & Ps'))
# def one_step_abstraction_to_ltl(predAbs):
#     one_step_abstraction = to_automaton_one_step(predAbs)
#     print(one_step_abstraction.to_dot())
#     predicates = predAbs.state_predicates + predAbs.transition_predicates
#
#     new_env_transitions = one_step_abstraction.env_transitions
#     new_con_transitions = one_step_abstraction.con_transitions
#
#     ltl_to_program_transitions = {}
#
#     init_transitions = [t for t in new_env_transitions if t.src == one_step_abstraction.initial_state]
#     init_cond_formula_sets = []
#     ltl_to_program_transitions["init"] = {}
#     for t in init_transitions:
#         cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
#                         conjunct_formula_set(
#                             sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
#                         )
#         init_cond_formula_sets.append(cond)
#
#     init_cond_formula = disjunct_formula_set(init_cond_formula_sets)
#
#     init_cond = init_cond_formula.to_nuxmv()
#
#     states = [Variable(s.state) for s in one_step_abstraction.states if s != one_step_abstraction.initial_state] + \
#              [Variable(one_step_abstraction.initial_state)]
#     states = set(states)
#
#     at_least_and_at_most_one_state = UniOp("G",
#                                            conjunct_formula_set(
#                                                [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
#                                                                                      states
#                                                                                      if
#                                                                                      r != q]))
#                                                 for q in states if "loop" not in str(q)])).to_nuxmv()
#
#     not_init_env_transitions = [t for t in new_env_transitions if
#                                 t.src != one_step_abstraction.initial_state]
#
#     not_init_con_transitions = [t for t in new_con_transitions if
#                                 t.src != one_step_abstraction.initial_state]
#
#     matching_pairs = {}
#
#     # for every state that is not the initial state: s
#     # for each controller transition from that state: t
#     # get the set of all env transitions that can happen immediately after: ets
#     # and match s with the pair of condition of t and ets
#     #
#     # at the end, every state s is associated with a list of conditions
#     # and the associated env transitions that can happen after
#
#     preds_now_to_next = {}
#     # preds_now_to_next_pred_obligs = {}
#     for t in not_init_con_transitions:
#         current_preds = t.src.predicates
#         current_pred_state = conjunct_formula_set(label_preds(t.src.predicates, predicates), sort=True)
#         if current_pred_state not in preds_now_to_next.keys():
#             preds_now_to_next[current_pred_state] = {}
#
#         con_tran_preds = set()
#         for o in t.output:
#             if 'prev' in str(o):
#                 con_tran_preds.add(o)
#
#         for et in not_init_env_transitions:
#             if et.src.compatible(t.tgt, predAbs.program.symbol_table):
#                 next_pred_oblig = conjunct_formula_set(
#                     [iff(label_pred(p, predicates), X(label_pred(p, predicates))) for p in predicates if
#                      (p not in t.src.predicates + et.tgt.predicates and neg(
#                          p) not in t.src.predicates + et.tgt.predicates)])
#
#                 et_current_out = set()
#                 et_tran_preds = set()
#                 for o in et.output:
#                     if 'prev' in str(o):
#                         et_tran_preds.add(o)
#                     else:
#                         et_current_out.add(o)
#                 bookkept_tran_preds = bookkeep_tran_preds(con_tran_preds, et_tran_preds)
#
#                 next_state = bookkept_tran_preds | label_preds(et.tgt.predicates, predicates)
#                 next_state = conjunct_formula_set(next_state, sort=True)
#                 next_here = conjunct_formula_set({Variable(et.tgt.state)} | et_current_out)
#
#                 if next_state not in preds_now_to_next[current_pred_state][t.src][t.condition][et.condition].keys():
#                     preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state] = []
#                 preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state].append(
#                     conjunct(X(next_here), next_pred_oblig))
#
#     transitions = []
#     for Ps, state_dict in preds_now_to_next.items():
#         ps_transitions = []
#         relevant_states = set()
#         for q, events_dict in state_dict.items():
#             q_trans = []
#             for Cs, ets_dict in events_dict.items():
#                 con_trans = []
#                 for Es in ets_dict.keys():
#                     ps_next_trans = []
#                     for next_Ps, next_here in ets_dict[Es].items():
#                         next = (conjunct(X(next_Ps), disjunct_formula_set(next_here)))
#                         ps_next_trans.append(next)
#                     next = disjunct_formula_set(ps_next_trans)
#                     now = (Es)
#                     con_trans.append(conjunct(now, next))
#                 # not sure this will do anything,
#                 # already handled with merge transitions
#                 # next_state = simplify_formula_without_math(disjunct_formula_set(con_trans))
#                 # next = X(next_state)
#                 now = (Cs)
#                 q_trans.append(conjunct(now, next))
#             next = disjunct_formula_set(q_trans)
#             # next = conjunct(next, next_pred_oblig)#preds_now_to_next_pred_obligs[Ps])
#             now = Variable(q.state)
#             relevant_states.add(q.state)
#             ps_transitions.append(implies(now, next))
#         irrelevant_states = [neg(Variable(q)) for q in predAbs.program.states if q not in relevant_states]
#         next = conjunct_formula_set(ps_transitions)
#         # now = Ps
#         now = conjunct_formula_set([Ps] + irrelevant_states)
#         transitions.append(G(implies(now, next)))
#
#     return [init_cond, at_least_and_at_most_one_state] + transitions, ltl_to_program_transitions


# structure: G (Ps -> Cs -> Es -> Q ->  Q' -> Ps')
    # in the hope of a reduced explosion,
    # the other abstraction reproduces the powersets of predicates and env + con actions for each transition
    # This seems like a success! it is producing much smaller abstractions for the cinderella example;
    # but not as small as the two-step one (which benefits from invariants; although synthesis wise they both timeout)
def one_step_abstraction_to_ltl_alternate(predAbs):
    # This requires the abstraction to be explicit (no invars ignored in states)
    one_step_abstraction = to_automaton_one_step(predAbs)
    print(one_step_abstraction.to_dot())
    predicates = predAbs.get_state_predicates + predAbs.get_transition_predicates

    new_env_transitions = one_step_abstraction.env_transitions
    new_con_transitions = one_step_abstraction.con_transitions

    ltl_to_program_transitions = {}

    init_transitions = [t for t in new_env_transitions if t.src == one_step_abstraction.initial_state]
    init_cond_formula_sets = []
    ltl_to_program_transitions["init"] = {}
    for t in init_transitions:
        cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                        conjunct_formula_set(
                            sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                        )
        init_cond_formula_sets.append(cond)

    init_cond_formula = disjunct_formula_set(init_cond_formula_sets)

    init_cond = init_cond_formula.to_nuxmv()

    states = [Variable(s.state) for s in one_step_abstraction.states if s != one_step_abstraction.initial_state] + \
             [Variable(one_step_abstraction.initial_state)]
    states = set(states)

    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set(
                                               [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                     states
                                                                                     if
                                                                                     r != q]))
                                                for q in states if "loop" not in str(q)])).to_nuxmv()

    not_init_env_transitions = [t for t in new_env_transitions if
                                t.src != one_step_abstraction.initial_state]

    not_init_con_transitions = [t for t in new_con_transitions if
                                t.src != one_step_abstraction.initial_state]

    matching_pairs = {}

    # for every state that is not the initial state: s
    # for each controller transition from that state: t
    # get the set of all env transitions that can happen immediately after: ets
    # and match s with the pair of condition of t and ets
    #
    # at the end, every state s is associated with a list of conditions
    # and the associated env transitions that can happen after

    preds_now_to_next = {}
    # preds_now_to_next_pred_obligs = {}
    for t in not_init_con_transitions:
        current_pred_state = conjunct_formula_set(label_preds(t.src.predicates, predicates), sort=True)
        if current_pred_state not in preds_now_to_next.keys():
            preds_now_to_next[current_pred_state] = {}

        con_tran_preds = set()
        for o in t.output:
            if 'prev' in str(o):
                con_tran_preds.add(o)

        if t.src not in preds_now_to_next[current_pred_state].keys():
            preds_now_to_next[current_pred_state][t.src] = {}
        if t.condition not in preds_now_to_next[current_pred_state][t.src].keys():
            preds_now_to_next[current_pred_state][t.src][t.condition] = {}

        # this can be optimised
        for et in not_init_env_transitions:
        # for et in one_step_abstraction.state_to_env[t.tgt]:
            if et.src.compatible(t.tgt, predAbs.get_program.symbol_table):
                if et.condition not in preds_now_to_next[current_pred_state][t.src][t.condition].keys():
                    preds_now_to_next[current_pred_state][t.src][t.condition][et.condition] = {}


                next_pred_oblig = conjunct_formula_set(
                    [iff(label_pred(p, predicates), X(label_pred(p, predicates))) for p in predicates
                     if "_prev" not in str(p) and
                     (p not in t.src.predicates + et.tgt.predicates and neg(p) not in t.src.predicates + et.tgt.predicates)])

                et_current_out = set()
                et_tran_preds = set()
                for o in et.output:
                    if 'prev' in str(o):
                        et_tran_preds.add(o)
                    else:
                        et_current_out.add(o)
                bookkept_tran_preds = bookkeep_tran_preds(con_tran_preds, et_tran_preds)

                next_state = bookkept_tran_preds | label_preds(et.tgt.predicates, predicates)
                next_state = conjunct_formula_set(next_state, sort=True)
                next_here = conjunct_formula_set({Variable(et.tgt.state)} | et_current_out)

                if next_state not in preds_now_to_next[current_pred_state][t.src][t.condition][et.condition].keys():
                    preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state] = []
                preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state].append(conjunct(X(next_here), next_pred_oblig))

    transitions = []
    for Ps, state_dict in preds_now_to_next.items():
        ps_transitions = []
        relevant_states = set()
        for q, events_dict in state_dict.items():
            q_trans = []
            for Cs, ets_dict in events_dict.items():
                con_trans = []
                ps_next_trans = []
                for Es in ets_dict.keys():
                    es_next_trans = []
                    for next_Ps, next_here in ets_dict[Es].items():
                        es_next_trans.append(conjunct(X(next_Ps), disjunct_formula_set(next_here)))
                    next = conjunct(X(Es), disjunct_formula_set(es_next_trans))
                    ps_next_trans.append(next)
                    con_trans.append(conjunct(X(Es), next))

                now = (Cs)
                q_trans.append(conjunct(now, disjunct_formula_set(ps_next_trans)))
            next = disjunct_formula_set(q_trans)
            # next = conjunct(next, next_pred_oblig)#preds_now_to_next_pred_obligs[Ps])
            now = Variable(q.state)
            relevant_states.add(q.state)
            ps_transitions.append(implies(now, next))
        irrelevant_states = [neg(Variable(q)) for q in predAbs.get_program.states if q not in relevant_states]
        next = conjunct_formula_set(ps_transitions)
        # now = Ps
        now = conjunct_formula_set([Ps] + irrelevant_states)
        transitions.append(G(implies(now, next)))

    return one_step_abstraction, [init_cond, at_least_and_at_most_one_state] + transitions, ltl_to_program_transitions

def one_step_abstraction_to_ltl(predAbs):
    one_step_abstraction = to_automaton_one_step(predAbs)
    print(one_step_abstraction.to_dot())
    predicates = predAbs.get_state_predicates + predAbs.get_transition_predicates

    new_env_transitions = one_step_abstraction.env_transitions
    new_con_transitions = one_step_abstraction.con_transitions

    init_transitions = [t for t in new_env_transitions if t.src == one_step_abstraction.initial_state]
    init_cond_formula_sets = []
    for t in init_transitions:
        cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                        conjunct_formula_set(
                            sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                        )
        init_cond_formula_sets.append(cond)

    init_cond_formula = disjunct_formula_set(init_cond_formula_sets)

    init_cond = init_cond_formula.to_nuxmv()

    states = [Variable(s.state) for s in one_step_abstraction.states if s != one_step_abstraction.initial_state] + \
             [Variable(one_step_abstraction.initial_state)]
    states = set(states)

    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set(
                                               [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                     states
                                                                                     if
                                                                                     r != q]))
                                                for q in states if "loop" not in str(q)])).to_nuxmv()

    not_init_env_transitions = [t for t in new_env_transitions if
                                t.src != one_step_abstraction.initial_state]

    not_init_con_transitions = [t for t in new_con_transitions if
                                t.src != one_step_abstraction.initial_state]

    matching_pairs = {}

    # for every state that is not the initial state: s
    # for each controller transition from that state: t
    # get the set of all env transitions that can happen immediately after: ets
    # and match s with the pair of condition of t and ets
    #
    # at the end, every state s is associated with a list of conditions
    # and the associated env transitions that can happen after

    preds_now_to_next = {}
    # preds_now_to_next_pred_obligs = {}
    for t in not_init_con_transitions:
        con_tran_preds = set()
        for o in t.output:
            if 'prev' in str(o):
                con_tran_preds.add(o)

        # this can be optimised
        for et in not_init_env_transitions:
        # for et in one_step_abstraction.state_to_env[t.tgt]:
            if et.src.compatible(t.tgt, predAbs.get_program.symbol_table):
                src_preds = [p for p in t.src.predicates] + \
                            [p for p in et.src.predicates if p not in t.tgt.predicates and neg(p) not in t.tgt.predicates]
                current_pred_state = conjunct_formula_set(label_preds(src_preds, predicates), sort=True)

                if current_pred_state not in preds_now_to_next.keys():
                    preds_now_to_next[current_pred_state] = {}

                if t.src not in preds_now_to_next[current_pred_state].keys():
                    preds_now_to_next[current_pred_state][t.src] = {}
                if t.condition not in preds_now_to_next[current_pred_state][t.src].keys():
                    preds_now_to_next[current_pred_state][t.src][t.condition] = {}

                if et.condition not in preds_now_to_next[current_pred_state][t.src][t.condition].keys():
                    preds_now_to_next[current_pred_state][t.src][t.condition][et.condition] = {}


                next_pred_oblig = conjunct_formula_set(
                    [iff(label_pred(p, predicates), X(label_pred(p, predicates))) for p in predicates
                     if "_prev" not in str(p) and
                     (p not in t.src.predicates + et.tgt.predicates and neg(p) not in t.src.predicates + et.tgt.predicates)])

                et_current_out = set()
                et_tran_preds = set()
                for o in et.output:
                    if 'prev' in str(o):
                        et_tran_preds.add(o)
                    else:
                        et_current_out.add(o)
                bookkept_tran_preds = bookkeep_tran_preds(con_tran_preds, et_tran_preds)

                next_state = bookkept_tran_preds | label_preds(et.tgt.predicates, predicates)
                next_state = conjunct_formula_set(next_state, sort=True)
                next_here = conjunct_formula_set({Variable(et.tgt.state)} | et_current_out)

                if next_state not in preds_now_to_next[current_pred_state][t.src][t.condition][et.condition].keys():
                    preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state] = []
                preds_now_to_next[current_pred_state][t.src][t.condition][et.condition][next_state].append(conjunct(X(next_here), next_pred_oblig))

    transitions = []
    for Ps, state_dict in preds_now_to_next.items():
        ps_transitions = []
        relevant_states = set()
        for q, events_dict in state_dict.items():
            q_trans = []
            for Cs, ets_dict in events_dict.items():
                con_trans = []
                ps_next_trans = []
                for Es in ets_dict.keys():
                    es_next_trans = []
                    for next_Ps, next_here in ets_dict[Es].items():
                        es_next_trans.append(conjunct(X(next_Ps), disjunct_formula_set(next_here)))
                    next = conjunct(X(Es), disjunct_formula_set(es_next_trans))
                    ps_next_trans.append(next)
                    con_trans.append(conjunct(X(Es), next))

                now = (Cs)
                q_trans.append(conjunct(now, disjunct_formula_set(ps_next_trans)))
            next = disjunct_formula_set(q_trans)
            # next = conjunct(next, next_pred_oblig)#preds_now_to_next_pred_obligs[Ps])
            now = Variable(q.state)
            relevant_states.add(q.state)
            ps_transitions.append(implies(now, next))
        irrelevant_states = [neg(Variable(q)) for q in predAbs.get_program.states if q not in relevant_states]
        next = conjunct_formula_set(ps_transitions)
        # now = Ps
        now = conjunct_formula_set([Ps] + irrelevant_states)
        transitions.append(G(implies(now, next)))

    return one_step_abstraction, [init_cond, at_least_and_at_most_one_state] + transitions, None


def one_step_abstraction_to_combined_transition(predAbs):
    one_step_abstraction = to_automaton_one_step(predAbs)

    init_transitions = [t for t in one_step_abstraction.env_transitions if t.src == one_step_abstraction.initial_state]
    init_states = set()
    for t in init_transitions:
        init_states.add(t.tgt)

    states = set()

    not_init_env_transitions = [t for t in one_step_abstraction.env_transitions if
                                t.src != one_step_abstraction.initial_state]

    not_init_con_transitions = [t for t in one_step_abstraction.con_transitions]

    # for every state that is not the initial state: s
    # for each controller transition from that state: t
    # get the set of all env transitions that can happen immediately after: ets
    # and match s with the pair of condition of t and ets
    #
    # at the end, every state s is associated with a list of conditions
    # and the associated env transitions that can happen after
    state_to_transitions = {}

    for t in not_init_con_transitions:
        state_to_transitions[t.src] = set()

        con_tran_preds = set()
        for o in t.output:
            if 'prev' in str(o):
                con_tran_preds.add(o)

        # TODO this can be improved, using the state to trans dict
        for et in not_init_env_transitions:
            # if et.src.state == t.tgt.state and set(et.src.predicates).issubset(set(t.tgt.predicates)):
            if et.src == t.tgt:
                et_current_out = set()
                et_tran_preds = set()
                for o in et.output:
                    if 'prev' in str(o):
                        et_tran_preds.add(o)
                    else:
                        et_current_out.add(o)
                bookkept_tran_preds = bookkeep_tran_preds(con_tran_preds, et_tran_preds)

                new_t = Transition(t.src, conjunct(t.condition, et.condition), [], bookkept_tran_preds, et.tgt)
                states.add(t.src)
                states.add(et.tgt)

                state_to_transitions[t.src].add(new_t)
    return init_states, states, state_to_transitions
