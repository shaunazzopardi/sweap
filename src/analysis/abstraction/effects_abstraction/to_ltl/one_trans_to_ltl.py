import time

import config
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction

from prop_lang.util import atomic_predicates, G, X, conjunct_formula_set, conjunct, \
    disjunct_formula_set, implies, F, propagate_nexts, disjunct, massage_ltl_for_dual, neg
from prop_lang.variable import Variable
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem


def to_ltl_organised_by_pred_effects_guard_updates(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: x.replace_formulas(predicate_abstraction.var_relabellings)
    program = predicate_abstraction.program

    init_explicit_state = program.states_binary_map[predicate_abstraction.program.initial_state]

    init_preds = [rename_pred(p) for p in predicate_abstraction.init_state_abstraction]
    #
    # init_state = conjunct(init_explicit_state, conjunct_formula_set(init_preds))

    # pred_next = set()
    dualise = config.Config.getConfig().dual
    # for gu, post in predicate_abstraction.second_state_abstraction.items():
    #     for t in predicate_abstraction.gu_to_trans[gu]:
    #         E_formula = t.condition.replace_formulas(predicate_abstraction.var_relabellings)
    #         if dualise:
    #             E_formula = massage_ltl_for_dual(E_formula, predicate_abstraction.program.inputs)
    #         next_preds = [rename_pred(p) for p in post]
    #
    #         pred_next.add(conjunct((conjunct_formula_set([E_formula])),
    #                                propagate_nexts(X(conjunct_formula_set(next_preds + [program.states_binary_map[t.tgt]])))))
    #
    # init_transition_ltl = disjunct_formula_set(pred_next)

    next_bins = []
    if dualise:
        for ch_pred in predicate_abstraction.v_to_chain_pred.values():
            if ch_pred.is_input:
                next_bins.extend(ch_pred.bin_rep.values())

    init_transition_ltl = []
    transition_ltl = {}
    for gu in predicate_abstraction.gu_to_trans.keys():
        t = predicate_abstraction.gu_to_trans[gu][0]
        if t in predicate_abstraction.init_program_trans:
            cond = predicate_abstraction.init_program_trans_to_orig[t].condition
        else:
            cond = t.condition

        if dualise:
            cond = massage_ltl_for_dual(cond, predicate_abstraction.program.inputs, False)

        cond = cond.replace_formulas(predicate_abstraction.var_relabellings)
        effect = predicate_abstraction.abstract_effect_ltl[gu]
        if dualise:
            effect = massage_ltl_for_dual(effect, predicate_abstraction.program.inputs, False)

        for t in predicate_abstraction.gu_to_trans[gu]:
            guard = program.states_binary_map[t.src]

            pred_effect_formula = effect
            if len(t.output) > 0:
                output_formula = conjunct_formula_set([X(o) for o in t.output])
                effect_formula = conjunct(pred_effect_formula, output_formula)
            else:
                effect_formula = pred_effect_formula

            bin_tgt = program.states_binary_map[t.tgt]
            next = conjunct(effect_formula, propagate_nexts(X(bin_tgt)))

            if t in predicate_abstraction.init_program_trans:
                init_transition_ltl.append(conjunct(cond, next))

            if t in predicate_abstraction.non_init_program_trans:
                if guard in transition_ltl.keys():
                    transition_ltl[guard] = disjunct(transition_ltl[guard], conjunct(cond, next))
                else:
                    transition_ltl[guard] = conjunct(cond, next)

    _transition_ltl = [(G(implies(g, transition_ltl[g]))) for g in
                           transition_ltl.keys()]

    init_transition_ltl = disjunct_formula_set(init_transition_ltl)

    abs = [init_explicit_state] + init_preds + [init_transition_ltl] + _transition_ltl
    bin_sanity_condition = []
    # if dualise:
    #     for ch_pred in predicate_abstraction.v_to_chain_pred.values():
    #         if ch_pred.is_input:
    #             cond = disjunct_formula_set(ch_pred.bin_rep.values())
    #             bin_sanity_condition.append(G(cond))
    #     if len(bin_sanity_condition) > 0:
    #         return neg(conjunct_formula_set(bin_sanity_condition)), abs
    #     else:
    #         return None, abs
    # else:
    return None, abs



def abstract_ltl_problem(original_LTL_problem: LTLSynthesisProblem,
                         effects_abstraction: EffectsAbstraction):
    start = time.time()
    # ltl_abstraction = to_ltl_reduced(effects_abstraction)
    controller_fail, ltl_abstraction = to_ltl_organised_by_pred_effects_guard_updates(effects_abstraction)
    print("ltl abstraction took: " + str(time.time() - start))
    env_predicate_vars = set()
    con_predicate_vars = set()
    dualise = config.Config.getConfig().dual
    for p in effects_abstraction.state_predicates:
        if dualise:
            if any(v for v in p.variablesin() if v in effects_abstraction.program.num_in_out):
                con_predicate_vars.add(p.bool_var)
            else:
                env_predicate_vars.add(p.bool_var)
        else:
            env_predicate_vars.add(p.bool_var)
    for p in effects_abstraction.transition_predicates:
        env_predicate_vars.update(p.bool_rep.values())

    for _, p in effects_abstraction.v_to_chain_pred.items():
        if dualise:
            if any(v for v in p.variablesin() if v in effects_abstraction.program.num_in_out):
                con_predicate_vars.update(p.bin_vars)
            else:
                env_predicate_vars.update(p.bin_vars)
        else:
            env_predicate_vars.update(p.bin_vars)

    program = effects_abstraction.get_program()
    env_pred_props = program.bin_state_vars + list(env_predicate_vars)
    con_pred_props = con_predicate_vars

    states_binary_map = {Variable(k): v for k, v in program.states_binary_map.items()}
    dict_to_replace = states_binary_map
    dict_to_replace |= effects_abstraction.var_relabellings

    loop_vars = []
    loop_constraints = []
    # TODO need to get rankings from chain preds
    for dec, ltl_constraints in effects_abstraction.ranking_constraints.items():
        f = implies(G(F(dec)), propagate_nexts(conjunct_formula_set(ltl_constraints)))
        f = f.replace_formulas(dict_to_replace)
        loop_constraints.append(f)
        all_preds = set()
        all_preds |= atomic_predicates(f)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])
    for chain_pred in effects_abstraction.v_to_chain_pred.values():
        top_ranking = chain_pred.top_ranking
        if not top_ranking is None:
            loop_constraints.append(top_ranking.replace_formulas(dict_to_replace))
        bottom_ranking = chain_pred.bottom_ranking
        if not bottom_ranking is None:
            loop_constraints.append(bottom_ranking.replace_formulas(dict_to_replace))

    for f in effects_abstraction.structural_loop_constraints:
        f = propagate_nexts(f.replace_formulas(dict_to_replace))
        loop_constraints.append(f)
        all_preds = set()
        all_preds |= atomic_predicates(f)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])

    for p in loop_vars:
        if dualise:
            if any(v for v in p.variablesin() if v in effects_abstraction.program.num_in_out):
                con_predicate_vars.add(p)
            else:
                env_predicate_vars.add(p)
        else:
            env_predicate_vars.add(p)

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

    env_pred_props = {str(v) for v in env_pred_props}
    con_pred_props = {str(v) for v in con_pred_props}

    env_props = []
    for v in original_LTL_problem.env_props:
        if isinstance(v, tuple) and v[1].startswith("bool"):
            env_props.append(v[0])
    con_props = []
    for v in original_LTL_problem.con_props:
        if isinstance(v, tuple) and v[1].startswith("bool"):
            con_props.append(v[0])

    # if controller_fail is not None:
    #     assumptions = [disjunct(controller_fail, conjunct_formula_set(assumptions))]
    #     guarantees += [neg(controller_fail)]

    ltl_synthesis_problem = AbstractLTLSynthesisProblem(env_props,
                                                        program.out_events,
                                                        list(env_pred_props),
                                                        con_props + list(con_pred_props),
                                                        assumptions,
                                                        guarantees)

    return ltl_synthesis_problem
