import time

import multiprocessing as mp
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from analysis.abstraction.effects_abstraction.to_ltl.to_env_con_separate_ltl import empty_abstraction

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import atomic_predicates, G, X, label_pred, neg, conjunct_formula_set, conjunct, \
    disjunct_formula_set, iff, simplify_formula_without_math, cnf_safe, implies, sat, true, bdd_simplify_ltl_formula, \
    is_true
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem


def to_ltl_organised_by_pred_effects_guard_updates(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: label_pred(x, predicate_abstraction.get_all_preds())

    # TODO try to put LTL inform of list of G(now -> next), see if it helps
    pred_next = set()
    for i, (gu, tgt) in enumerate(predicate_abstraction.init_disjuncts):
        post = predicate_abstraction.second_state_abstraction[i]
        E_formula = disjunct_formula_set([conjunct_formula_set(E) for E in predicate_abstraction.init_gu_to_E[gu]])

        post_renamed = [rename_pred(p) for p in post]

        pred_next.add(conjunct((conjunct_formula_set([E_formula])),
                               X(conjunct_formula_set(post_renamed + [Variable(tgt)]))))

    init_state = conjunct_formula_set([Variable(predicate_abstraction.program.initial_state)] +
                  [rename_pred(p) for p in predicate_abstraction.init_state_abstraction])

    init_transition_ltl = disjunct_formula_set(pred_next)

    transition_ltl = {}
    for trans in predicate_abstraction.non_init_program_trans:
        pred_effects = []

        u = predicate_abstraction.trans_to_u[trans]
        constant_tran_preds = []
        for p in predicate_abstraction.u_constants[u]:
            if isinstance(p, UniOp) and p.op == "!":
                constant_tran_preds += [(neg(rename_pred(p.right)))]
            else:
                constant_tran_preds += [(rename_pred(p))]

        for gu, Es in predicate_abstraction.transition_guard_update_to_E[trans].items():
            effect = predicate_abstraction.abstract_effect_ltl[gu]
            invar_preds_effects = []

            if gu in predicate_abstraction.abstract_effect_invars.keys():
                invar_preds_effects += [iff(rename_pred(p), X(rename_pred(p))) for p in
                                        set(predicate_abstraction.abstract_effect_invars[gu])]

            if gu in predicate_abstraction.abstract_effect_constant.keys():
                invar_preds_effects += [X(rename_pred(p)) for p in
                                        set(predicate_abstraction.abstract_effect_constant[gu])]

            if gu in predicate_abstraction.abstract_effect_tran_preds_constant.keys():
                invar_preds_effects += [X(rename_pred(p)) for p in
                                        set(predicate_abstraction.abstract_effect_tran_preds_constant[gu])]

            E_formula = disjunct_formula_set([conjunct_formula_set(E) for E in Es])
            E_formula = conjunct_formula_set([E_formula] + invar_preds_effects)
            E_effects = []
            for next_pred_state, E_now_simplified in effect.items():

                E_next = conjunct_formula_set([rename_pred(p) for p in next_pred_state])
                E_next_simplified = simplify_formula_without_math(E_next)
                E_effects.append(conjunct(E_now_simplified, X(E_next_simplified)))
            pred_effects.extend([conjunct(E_formula, (disjunct_formula_set(E_effects)))])

        pred_effect_formula = disjunct_formula_set(pred_effects)
        if len(trans.output) > 0:
            output_formula = conjunct_formula_set([X(o) for o in trans.output])
            effect_formula = conjunct(pred_effect_formula, output_formula)
        else:
            effect_formula = pred_effect_formula

        if len(constant_tran_preds) > 0:
            constant_tran_preds = conjunct_formula_set([X((p)) for p in constant_tran_preds])
            effect_formula = conjunct(effect_formula, constant_tran_preds)
        else:
            effect_formula = pred_effect_formula

        next = conjunct(effect_formula, X(Variable(trans.tgt)))

        if trans.src in transition_ltl.keys():
            transition_ltl[trans.src].append(next)
        else:
            transition_ltl[trans.src] = [next]

    _transition_ltl = [(G(implies(Variable(src), disjunct_formula_set(transition_ltl[src])))) for src in
                           transition_ltl.keys()]

    program = predicate_abstraction.get_program()
    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set(
                                               [BiOp(Variable(q), "<=>", conjunct_formula_set([neg(Variable(r)) for r in
                                                                                     program.states
                                                                                     if
                                                                                     r != q]))
                                                for q in program.states if "loop" not in str(q)])).to_nuxmv()


    # logger.info("LTL formula: " + str(ltl))
    return [init_state, init_transition_ltl, at_least_and_at_most_one_state] + _transition_ltl


def to_ltl_reduced(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: label_pred(x, predicate_abstraction.get_all_preds())

    pred_next = {}
    for t in predicate_abstraction.init_program_trans:
        for E, effect in predicate_abstraction.abstract_effect[t].items():
            if len(effect.keys()) > 1:
                raise Exception("init transition " + str(t) + " has more than one possible effect")
            elif len(effect.keys()) == 1:
                E_effects = {rename_pred(p) for p in list(effect.keys())[0]}
            else:
                E_effects = set()
            E_effects.update({neg(rename_pred(p)) for p in predicate_abstraction.abstract_effect_invars[t]})
            E_effects.update({rename_pred(p) for p in predicate_abstraction.abstract_effect_constant[t]})
            E_effects.update({rename_pred(p) for p in predicate_abstraction.abstract_effect_tran_preds_constant[t]})
            if not empty_abstraction(predicate_abstraction) and len(E_effects) == 0:
                raise Exception("init transition " + str(t) + " has no effect")
            if frozenset(E_effects) not in pred_next.keys():
                pred_next[frozenset(E_effects)] = set()
            pred_next[frozenset(E_effects)].add(conjunct((conjunct_formula_set(E)),
                                                         X(conjunct_formula_set([Variable(t.tgt)] + t.output))))

    init_program_formula = conjunct_formula_set(BiOp(Variable(tv.name), "=", tv.value) for tv in predicate_abstraction.program.valuation)
    init_preds = [p for p in predicate_abstraction.state_predicates if sat(conjunct(init_program_formula, p),
                                                                           predicate_abstraction.symbol_table)]
    init_preds += [neg(p) for p in predicate_abstraction.state_predicates if p not in init_preds]
    init_preds += [neg(p) for p in predicate_abstraction.transition_predicates]
    init_preds = list(map(rename_pred, init_preds))
    init_preds += [Variable(predicate_abstraction.program.initial_state)]
    init_formula = conjunct_formula_set(init_preds)

    init_transition_ltls = []
    for E_effects in pred_next.keys():
        init_transition_ltls.append(conjunct(conjunct_formula_set(X(preds) for preds in E_effects),
                                            disjunct_formula_set([(phi) for phi in pred_next[E_effects]])))
    init_transition_ltl = disjunct_formula_set(init_transition_ltls)

    transition_ltl = {}
    for trans in predicate_abstraction.abstract_guard.keys():
        # exclude initial transitions
        if trans in predicate_abstraction.init_program_trans: continue
        invar_preds_effects = []

        if trans in predicate_abstraction.abstract_effect_invars.keys():
            invar_preds_effects += [iff(rename_pred(p), X(rename_pred(p))) for p in
                                    set(predicate_abstraction.abstract_effect_invars[trans])]

        if trans in predicate_abstraction.abstract_effect_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_constant[trans])]

        if trans in predicate_abstraction.abstract_effect_tran_preds_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_tran_preds_constant[trans])]

        invar_preds_formula = conjunct_formula_set(invar_preds_effects)
        pred_effects = []

        for E, effect in predicate_abstraction.abstract_effect[trans].items():
            E_effects = []
            for next_pred_state, pred_states in effect.items():
                E_now = disjunct_formula_set(
                    [conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states])
                E_now_simplified = simplify_formula_without_math(E_now)
                if config.Config.getConfig().cnf_optimisations:
                    E_now_simplified = cnf_safe(E_now_simplified)

                E_next = conjunct_formula_set([rename_pred(p) for p in next_pred_state])
                E_next_simplified = simplify_formula_without_math(E_next)
                E_effects.extend([conjunct(E_now_simplified, X(E_next_simplified))])
            pred_effects.extend([conjunct(conjunct_formula_set(E), (disjunct_formula_set(E_effects)))])

        pred_effect_formula = disjunct_formula_set(pred_effects)
        output_formula = conjunct_formula_set([X(o) for o in trans.output])
        # output_formula = conjunct_formula_set([X(o) for o in env_trans.output])
        effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

        next = conjunct(effect_formula, X(Variable(trans.tgt)))

        if trans.src in transition_ltl.keys():
            transition_ltl[trans.src].append(next)
        else:
            transition_ltl[trans.src] = [next]

    _transition_f_ltl = []
    srcs = []
    for src in transition_ltl.keys():
        formula = disjunct_formula_set(transition_ltl[src])
        _transition_f_ltl.append(formula)
        srcs.append(src)

    with Pool(config.Config.getConfig().workers) as pool:
        results = pool.map(simplify_ltl, _transition_f_ltl)

        _transition_ltl = [G(implies(srcs[i], f)) for i, f in enumerate(results)]

    program = predicate_abstraction.get_program()
    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set(
                                               [BiOp(Variable(q), "<=>", conjunct_formula_set([neg(Variable(r)) for r in
                                                                                     program.states
                                                                                     if
                                                                                     r != q]))
                                                for q in program.states if "loop" not in str(q)])).to_nuxmv()


    # logger.info("LTL formula: " + str(ltl))
    return [init_formula, init_transition_ltl, at_least_and_at_most_one_state] + _transition_ltl


def abstract_ltl_problem(original_LTL_problem: LTLSynthesisProblem,
                         effects_abstraction: EffectsAbstraction):
    start = time.time()
    # ltl_abstraction = to_ltl_reduced(effects_abstraction)
    ltl_abstraction = to_ltl_organised_by_pred_effects_guard_updates(effects_abstraction)
    print("ltl abstraction took: " + str(time.time() - start))
    predicate_vars = set(effects_abstraction.var_relabellings.values())

    program = effects_abstraction.get_program()
    pred_props = [Variable(s) for s in program.states] \
                 + list(predicate_vars)

    loop_vars = []
    for ltl_constraint in effects_abstraction.ltl_constraints:
        all_preds = atomic_predicates(ltl_constraint)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])

    pred_props.extend(list(set(loop_vars)))
    pred_props = list(set(pred_props))

    assumptions = effects_abstraction.ltl_constraints + ltl_abstraction + original_LTL_problem.assumptions
    guarantees = original_LTL_problem.guarantees

    ltl_synthesis_problem = AbstractLTLSynthesisProblem(original_LTL_problem.env_props,
                                                        program.out_events,
                                                        pred_props,
                                                        original_LTL_problem.con_props,
                                                        assumptions,
                                                        guarantees)

    return ltl_synthesis_problem


def simplify_ltl(formula):
    return bdd_simplify_ltl_formula(formula)