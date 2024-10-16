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
            gu_ltl = predicate_abstraction.abstract_effect_ltl[gu]
            pred_effects.append(conjunct(disjunct_formula_set([conjunct_formula_set(E) for E in Es]), gu_ltl))

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
