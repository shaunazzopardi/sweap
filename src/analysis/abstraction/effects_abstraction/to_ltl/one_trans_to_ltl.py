import time

import multiprocessing as mp
from multiprocessing import Pool

import config
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import atomic_predicates, G, X, label_pred, neg, conjunct_formula_set, conjunct, \
    disjunct_formula_set, implies, F, propagate_nexts
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem


def to_ltl_organised_by_pred_effects_guard_updates(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: predicate_abstraction.var_relabellings[x]
    program = predicate_abstraction.program

    init_explicit_state = program.states_binary_map[predicate_abstraction.program.initial_state]

    init_preds = [rename_pred(p) for p in predicate_abstraction.init_state_abstraction]

    init_state = conjunct(init_explicit_state, conjunct_formula_set(init_preds))

    pred_next = set()
    for i, (gu, tgt) in enumerate(predicate_abstraction.init_disjuncts):
        post = predicate_abstraction.second_state_abstraction[i]
        E_formula = disjunct_formula_set([conjunct_formula_set(E) for E in predicate_abstraction.init_gu_to_E[gu]])

        next_preds = [rename_pred(p) for p in post]

        pred_next.add(conjunct((conjunct_formula_set([E_formula])),
                               propagate_nexts(X(conjunct_formula_set(next_preds + [program.states_binary_map[tgt]])))))

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
            constant_tran_preds = conjunct_formula_set([X(p) for p in constant_tran_preds])
            effect_formula = conjunct(effect_formula, constant_tran_preds)
        else:
            effect_formula = pred_effect_formula

        bin_tgt = program.states_binary_map[trans.tgt]
        next = conjunct(effect_formula, propagate_nexts(X(bin_tgt)))

        if trans.src in transition_ltl.keys():
            transition_ltl[trans.src].append(next)
        else:
            transition_ltl[trans.src] = [next]

    _transition_ltl = [(G(implies(program.states_binary_map[src], disjunct_formula_set(transition_ltl[src])))) for src in
                           transition_ltl.keys()]

    # logger.info("LTL formula: " + str(ltl))
    return [init_state, init_transition_ltl] + _transition_ltl


def abstract_ltl_problem(original_LTL_problem: LTLSynthesisProblem,
                         effects_abstraction: EffectsAbstraction):
    start = time.time()
    # ltl_abstraction = to_ltl_reduced(effects_abstraction)
    ltl_abstraction = to_ltl_organised_by_pred_effects_guard_updates(effects_abstraction)
    print("ltl abstraction took: " + str(time.time() - start))
    predicate_vars = set()
    for p in effects_abstraction.state_predicates:
        if p not in effects_abstraction.var_relabellings:
            raise Exception("Predicate not in var relabellings")
        else:
            predicate_vars.add(effects_abstraction.var_relabellings[p])

    predicate_vars.update([Variable(x) for v in effects_abstraction.current_bin_vars.values() for x in v])

    program = effects_abstraction.get_program()
    pred_props = program.bin_state_vars + list(predicate_vars)

    states_binary_map = {Variable(k): v for k, v in program.states_binary_map.items()}
    dict_to_replace = states_binary_map
    dict_to_replace |= effects_abstraction.var_relabellings


    loop_vars = []
    loop_constraints = []
    for dec, ltl_constraints in effects_abstraction.ranking_constraints.items():
        f = implies(G(F(dec)), propagate_nexts(conjunct_formula_set(ltl_constraints)))
        f = f.replace_formulas(dict_to_replace)
        loop_constraints.append(f)
        all_preds = set()
        all_preds |= atomic_predicates(f)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])


    for f in effects_abstraction.structural_loop_constraints:
        f = propagate_nexts(f.replace_formulas(dict_to_replace))
        loop_constraints.append(f)
        all_preds = set()
        all_preds |= atomic_predicates(f)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])

    pred_props.extend(list(set(loop_vars)))
    pred_props = list(set(pred_props))

    bool_vars = list(list(states_binary_map.values())[0].variablesin()) + [Variable(x) for v in effects_abstraction.current_bin_vars.values() for x in v] + program.env_events + program.con_events
    orig_assumptions = []
    for ass in original_LTL_problem.assumptions:
        new_ass = ass.replace_formulas(dict_to_replace)
        orig_assumptions.append(new_ass)

    orig_guarantees = []
    for guar in original_LTL_problem.guarantees:
        new_guar = guar.replace_formulas(dict_to_replace)
        orig_guarantees.append(new_guar)

    assumptions = (loop_constraints + ltl_abstraction + orig_assumptions)
    guarantees = orig_guarantees

    new_pred_props = {str(v) for v in pred_props}
    pred_props = [Variable(v) for v in new_pred_props]

    ltl_synthesis_problem = AbstractLTLSynthesisProblem(original_LTL_problem.env_props,
                                                        program.out_events,
                                                        list(set(pred_props)),
                                                        original_LTL_problem.con_props,
                                                        assumptions,
                                                        guarantees)

    return ltl_synthesis_problem
