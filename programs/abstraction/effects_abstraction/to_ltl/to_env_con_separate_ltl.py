from programs.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from programs.abstraction.interface.Config import env, con
from programs.synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from programs.synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from programs.util import var_to_predicate, add_prev_suffix, label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import neg, conjunct_formula_set, disjunct_formula_set, conjunct, X, iff, \
    simplify_formula_without_math, G, implies, disjunct, F, U, cnf_with_timeout
from prop_lang.value import Value
from prop_lang.variable import Variable


def empty_abstraction(predicate_abstraction: EffectsAbstraction):
    return len(predicate_abstraction.state_predicates) == 0 and \
             len(predicate_abstraction.transition_predicates) == 0

def to_env_con_separate_ltl(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: label_pred(x, predicate_abstraction.get_all_preds())

    # TODO try to put LTL inform of list of G(now -> next), see if it helps
    init_transitions = []
    for t in predicate_abstraction.init_program_trans:
        for E, effect in predicate_abstraction.abstract_effect[t].items():
            if len(effect.keys()) > 1:
                raise Exception("init transition " + str(t) + " has more than one possible effect")
            elif len(effect.keys()) == 1:
                E_effects = [rename_pred(p) for p in list(effect.keys())[0]]
            else:
                E_effects = []
            E_effects += [neg(rename_pred(p)) for p in predicate_abstraction.abstract_effect_invars[t]]
            E_effects += [rename_pred(p) for p in predicate_abstraction.abstract_effect_constant[t]]
            E_effects += [rename_pred(p) for p in predicate_abstraction.abstract_effect_tran_preds_constant[t]]
            if not empty_abstraction(predicate_abstraction) and len(E_effects) == 0:
                raise Exception("init transition " + str(t) + " has no effect")
            init_transitions += [conjunct_formula_set(E_effects + [Variable(t.tgt)] + list(E) + t.output)]

    init_transition_ltl = disjunct_formula_set([conjunct(phi, X(phi)) for phi in init_transitions])

    env_transition_ltl = {}
    for env_trans in predicate_abstraction.abstract_guard_env.keys():
        # exclude initial transitions
        if env_trans in predicate_abstraction.init_program_trans: continue
        invar_preds_effects = []

        if env_trans in predicate_abstraction.abstract_effect_invars.keys():
            invar_preds_effects += [iff(rename_pred(p), X(rename_pred(p))) for p in
                                    set(predicate_abstraction.abstract_effect_invars[env_trans])]

        if env_trans in predicate_abstraction.abstract_effect_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_constant[env_trans])]

        if env_trans in predicate_abstraction.abstract_effect_tran_preds_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_tran_preds_constant[env_trans])]

        invar_preds_formula = conjunct_formula_set(invar_preds_effects)
        pred_effects = []

        for E, effect in predicate_abstraction.abstract_effect[env_trans].items():
            E_effects = []
            for next_pred_state, pred_states in effect.items():
                E_now = disjunct_formula_set(
                    [conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states])
                E_now_simplified = simplify_formula_without_math(E_now)
                E_now_simplified = cnf_with_timeout(E_now_simplified)

                E_next = conjunct_formula_set([rename_pred(p) for p in next_pred_state])
                E_next_simplified = simplify_formula_without_math(E_next)
                E_effects += [conjunct(E_now_simplified, X(E_next_simplified))]
            pred_effects += [conjunct(conjunct_formula_set(E), disjunct_formula_set(E_effects))]

        pred_effect_formula = disjunct_formula_set(pred_effects)
        output_formula = conjunct_formula_set([X(o) for o in env_trans.output])
        # output_formula = conjunct_formula_set([X(o) for o in env_trans.output])
        effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

        next = conjunct(effect_formula, X(conjunct_formula_set([Variable(env_trans.tgt)])))

        if env_trans.src in env_transition_ltl.keys():
            env_transition_ltl[env_trans.src].append(next)
        else:
            env_transition_ltl[env_trans.src] = [next]

    con_transition_ltl = {}
    for con_trans in predicate_abstraction.abstract_guard_con.keys():
        invar_preds_effects = []

        if con_trans in predicate_abstraction.abstract_effect_invars.keys():
            invar_preds_effects += [iff(rename_pred(p), X(rename_pred(p))) for p in
                                    set(predicate_abstraction.abstract_effect_invars[con_trans])]

        if con_trans in predicate_abstraction.abstract_effect_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_constant[con_trans])]

        if con_trans in predicate_abstraction.abstract_effect_tran_preds_constant.keys():
            invar_preds_effects += [X(rename_pred(p)) for p in
                                    set(predicate_abstraction.abstract_effect_tran_preds_constant[con_trans])]

        invar_preds_formula = conjunct_formula_set(invar_preds_effects)

        pred_effects = []

        for E, effect in predicate_abstraction.abstract_effect[con_trans].items():
            E_effects = []
            for next_pred_state, pred_states in effect.items():
                E_now = disjunct_formula_set(
                    [conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states])
                E_now_simplified = simplify_formula_without_math(E_now)
                E_now_simplified = cnf_with_timeout(E_now_simplified)

                E_next = conjunct_formula_set([rename_pred(p) for p in next_pred_state])
                E_next_simplified = simplify_formula_without_math(E_next)
                E_effects += [conjunct(E_now_simplified, X(E_next_simplified))]
            pred_effects += [conjunct(conjunct_formula_set(E), disjunct_formula_set(E_effects))]
        pred_effect_formula = disjunct_formula_set(pred_effects)
        output_formula = conjunct_formula_set([X(neg(o)) for o in predicate_abstraction.program.out_events])
        effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

        next = conjunct(effect_formula, X(conjunct_formula_set([Variable(con_trans.tgt)])))

        if con_trans.src in con_transition_ltl.keys():
            con_transition_ltl[con_trans.src].append(next)
        else:
            con_transition_ltl[con_trans.src] = [next]

    _env_transition_ltl = [X(G(implies(conjunct(env, src), disjunct_formula_set(env_transition_ltl[src])))) for src in
                           env_transition_ltl.keys()]
    _con_transition_ltl = [X(G((implies(conjunct(con, src), disjunct_formula_set(con_transition_ltl[src]))))) for src in
                           con_transition_ltl.keys()]

    program = predicate_abstraction.get_program()
    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set(
                                               [BiOp(Variable(q), "<=>", conjunct_formula_set([neg(Variable(r)) for r in
                                                                                     program.states
                                                                                     if
                                                                                     r != q]))
                                                for q in program.states if "loop" not in str(q)])).to_nuxmv()


    # logger.info("LTL formula: " + str(ltl))
    return [init_transition_ltl, at_least_and_at_most_one_state] + _env_transition_ltl + _con_transition_ltl


def abstract_ltl_problem(original_LTL_problem: LTLSynthesisProblem,
                         effects_abstraction: EffectsAbstraction):
    ltl_abstraction = to_env_con_separate_ltl(effects_abstraction)

    predicate_vars = set()
    for interpolant in effects_abstraction.get_interpolants():
        predicate_vars.add(label_pred(interpolant, []))

    transition_fairness = []
    for ranking, invars in effects_abstraction.get_ranking_and_invars().items():
        dec = BiOp(add_prev_suffix(ranking), ">", ranking)
        inc = BiOp(add_prev_suffix(ranking), "<", ranking)

        dec_var = label_pred(dec, effects_abstraction.get_ranking_and_invars().keys())
        inc_var = label_pred(inc, effects_abstraction.get_ranking_and_invars().keys())

        invar_vars = [label_pred(invar, invars) for invar in invars]
        invar_formula = conjunct_formula_set(invar_vars)

        predicate_vars.add(dec_var)
        predicate_vars.add(inc_var)
        predicate_vars.update(invar_vars)

        transition_fairness.extend([
            implies(G(F(conjunct(invar_formula, dec_var))),
                    G(F((disjunct(inc_var, neg(invar_formula)))))).simplify()])


    program = effects_abstraction.get_program()
    pred_props = [Variable(s) for s in program.states] \
                + list(predicate_vars) \
                + [env]

    turn_logic = [env, G(iff(env, X(con)))]

    original_assumptions_expanded = [expand_ltl_to_env_con_steps(a, original_LTL_problem.env_props)
                                     for a in original_LTL_problem.assumptions]

    original_guarantees_expanded = [expand_ltl_to_env_con_steps(g, original_LTL_problem.env_props)
                                    for g in original_LTL_problem.guarantees]

    assumptions = turn_logic + transition_fairness + ltl_abstraction + original_assumptions_expanded
    guarantees = original_guarantees_expanded


    ltl_synthesis_problem = AbstractLTLSynthesisProblem(original_LTL_problem.env_props,
                                                        program.out_events,
                                                        pred_props,
                                                        original_LTL_problem.con_props,
                                                        assumptions,
                                                        guarantees)

    return ltl_synthesis_problem


def expand_ltl_to_env_con_steps_with_until(formula: Formula, env_events: [Variable]):
    rewritten_formula = formula.replace_vars(lambda x: x if not isinstance(x, Variable)
    else (U(con, conjunct(env, x))
          if x in env_events
          else U(env, conjunct(con, x))))
    return rewritten_formula


def expand_ltl_to_env_con_steps(formula: Formula, env_events: [Variable]):
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if formula in env_events:
            return formula
        else:
            return X(formula)
    elif isinstance(formula, UniOp):
        if formula.op == "X":
            return X(X(expand_ltl_to_env_con_steps(formula.right, env_events)))
        elif formula.op == "F":
            return F(conjunct(env, expand_ltl_to_env_con_steps(formula.right, env_events)))
        elif formula.op == "G":
            return G(implies(env, expand_ltl_to_env_con_steps(formula.right, env_events)))
        else:
            return UniOp(formula.op, expand_ltl_to_env_con_steps(formula.right, env_events))
    elif isinstance(formula, BiOp):
        if formula.op == "U":
            return U(implies(env, expand_ltl_to_env_con_steps(formula.left, env_events)),
                     conjunct(env, expand_ltl_to_env_con_steps(formula.right, env_events)))
        elif formula.op[0] == "&":
            return conjunct(expand_ltl_to_env_con_steps(formula.left, env_events),
                            expand_ltl_to_env_con_steps(formula.right, env_events))
        elif formula.op[0] == "|":
            return disjunct(expand_ltl_to_env_con_steps(formula.left, env_events),
                            expand_ltl_to_env_con_steps(formula.right, env_events))
        elif formula.op == "->":
            return implies(expand_ltl_to_env_con_steps(formula.left, env_events),
                           expand_ltl_to_env_con_steps(formula.right, env_events))
        elif formula.op == "<->":
            return iff(expand_ltl_to_env_con_steps(formula.left, env_events),
                       expand_ltl_to_env_con_steps(formula.right, env_events))
        else:
            raise Exception(f"Formula {formula} not supported yet.")
    else:
        raise Exception(f"Formula {formula} not supported yet.")