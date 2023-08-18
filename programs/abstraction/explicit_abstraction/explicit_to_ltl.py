from programs.util import label_preds, label_pred
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, conjunct_formula_set, disjunct_formula_set, iff, X, implies, neg, G
from prop_lang.variable import Variable


def explicit_to_state_based_ltl(predAbs):
    # This requires the abstraction to be explicit (no invars ignored in states)
    one_step_abstraction = predAbs.to_automaton_abstraction()
    print(one_step_abstraction.to_dot())
    predicates = predAbs.get_state_predicates() + predAbs.get_transition_predicates()

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
            if et.src.compatible(t.tgt, predAbs.get_program().symbol_table):
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
        irrelevant_states = [neg(Variable(q)) for q in predAbs.get_program().states if q not in relevant_states]
        next = conjunct_formula_set(ps_transitions)
        # now = Ps
        now = conjunct_formula_set([Ps] + irrelevant_states)
        transitions.append(G(implies(now, next)))

    return one_step_abstraction, [init_cond, at_least_and_at_most_one_state] + transitions

def bookkeep_tran_preds(con_tran_preds, env_tran_preds):
    if True:
        pos = {p for p in (con_tran_preds | env_tran_preds) if not isinstance(p, UniOp)}
        all_neg = {p for p in (con_tran_preds | env_tran_preds) if isinstance(p, UniOp)}
        neg = {p for p in all_neg if p.right not in pos}

        return (pos | neg)
