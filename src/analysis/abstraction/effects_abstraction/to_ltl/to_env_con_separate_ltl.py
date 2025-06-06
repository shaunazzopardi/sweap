from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from config import env, con, init_state
from prop_lang.mathexpr import MathExpr
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import neg, conjunct_formula_set, disjunct_formula_set, conjunct, X, iff, \
    simplify_formula_without_math, G, implies, disjunct, F, U, cnf_safe, flatten_effects, negate, label_pred, \
    atomic_predicates
from prop_lang.value import Value
from prop_lang.variable import Variable


def empty_abstraction(predicate_abstraction: EffectsAbstraction):
    return len(predicate_abstraction.state_predicates) == 0 and \
        len(predicate_abstraction.transition_predicates) == 0


def to_env_con_separate_ltl(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: (label_pred(x, predicate_abstraction.get_all_preds())
                                    if x not in predicate_abstraction.program.env_events + predicate_abstraction.program.con_events
                                        and negate(x) not in predicate_abstraction.program.env_events + predicate_abstraction.program.con_events
                                    else x)

    init_transitions = []
    pred_next = {}
    for t in predicate_abstraction.init_program_trans:
        for E, effect in predicate_abstraction.abstract_effect[t].items():
            if len(effect.keys()) > 1:
                raise Exception("init transition " + str(t) + " has more than one possible effect")
            elif len(effect.keys()) == 1:
                E_effects = {rename_pred(p) for p in list(effect.keys())[0]}
            else:
                E_effects = {}
            E_effects.update({rename_pred(p) for p in predicate_abstraction.abstract_effect_constant[t]})
            E_effects.update({rename_pred(p) for p in predicate_abstraction.abstract_effect_tran_preds_constant[t]})
            if not empty_abstraction(predicate_abstraction) and len(E_effects) == 0:
                raise Exception("init transition " + str(t) + " has no effect")
            if frozenset(E_effects) not in pred_next.keys():
                pred_next[frozenset(E_effects)] = set()
            pred_next[frozenset(E_effects)].add(conjunct_formula_set([Variable(t.tgt)] + list(E) + t.output))
            init_transitions.extend([conjunct_formula_set(list(E_effects) + [Variable(t.tgt)] + list(E) + t.output)])

    init_transition_ltls = []
    for E_effects in pred_next.keys():
        init_transition_ltls.append(conjunct(conjunct_formula_set(conjunct(preds, X(preds)) for preds in E_effects),
                                             disjunct_formula_set(
                                                 [conjunct(phi, X(phi)) for phi in pred_next[E_effects]])))
    init_transition_ltl = disjunct_formula_set(init_transition_ltls)

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

        all_effects = []
        for E, effect in predicate_abstraction.abstract_effect[env_trans].items():
            inverted_effects = effect.items_inverted()
            new_effects = [(set(now).union(E), nexts) for now, nexts in inverted_effects]
            all_effects.extend(new_effects)
            # E_effects = []
            # formula = flatten_effects(effect.items_inverted(), predicate_abstraction.state_predicates, rename_pred)
            # pred_effects += [conjunct(conjunct_formula_set(E), formula)]
        formula = flatten_effects(all_effects, predicate_abstraction.state_predicates, rename_pred)
        pred_effects.append(formula)

        pred_effect_formula = disjunct_formula_set(pred_effects)
        output_formula = conjunct_formula_set([X(o) for o in env_trans.output])
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
        all_effects = []
        for E, effect in predicate_abstraction.abstract_effect[con_trans].items():
            inverted_effects = effect.items_inverted()
            new_effects = [(set(now).union(E), nexts) for now, nexts in inverted_effects]
            all_effects.extend(new_effects)
            # E_effects = []
            # formula = flatten_effects(effect.items_inverted(), predicate_abstraction.state_predicates, rename_pred)
            # pred_effects += [conjunct(conjunct_formula_set(E), formula)]
        formula = flatten_effects(all_effects, predicate_abstraction.state_predicates, rename_pred)
        pred_effects.append(formula)

        pred_effect_formula = disjunct_formula_set(pred_effects)
        output_formula = conjunct_formula_set([X(neg(o)) for o in predicate_abstraction.program.out_events])
        effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

        next = conjunct(effect_formula, X(conjunct_formula_set([Variable(con_trans.tgt)])))

        if con_trans.src in con_transition_ltl.keys():
            con_transition_ltl[con_trans.src].append(next)
        else:
            con_transition_ltl[con_trans.src] = [next]

    _env_transition_ltl = [(G(implies(conjunct(conjunct(neg(init_state), env), src), disjunct_formula_set(env_transition_ltl[src])))) for src in
                           env_transition_ltl.keys()]
    _con_transition_ltl = [(G((implies(conjunct(conjunct(neg(init_state), con), src), disjunct_formula_set(con_transition_ltl[src]))))) for src in
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


def to_env_con_separate_ltl_organised_by_pred_effects(predicate_abstraction: EffectsAbstraction):
    rename_pred = lambda x: label_pred(x, predicate_abstraction.get_all_preds())

    # TODO try to put LTL inform of list of G(now -> next), see if it helps
    init_transitions = []
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
            pred_next[frozenset(E_effects)].add(conjunct_formula_set([Variable(t.tgt)] + list(E) + t.output))
            init_transitions.extend([conjunct_formula_set(list(E_effects) + [Variable(t.tgt)] + list(E) + t.output)])

    init_transition_ltls = []
    for E_effects in pred_next.keys():
        init_transition_ltls.append(conjunct(conjunct_formula_set(conjunct(preds, X(preds)) for preds in E_effects),
                                            disjunct_formula_set([conjunct(phi, X(phi)) for phi in pred_next[E_effects]])))
    init_transition_ltl = disjunct_formula_set(init_transition_ltls)

    env_transition_ltl = {}
    env_pred_effects = {}
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
                E_now_simplified = cnf_safe(E_now_simplified)

                E_next = conjunct_formula_set([rename_pred(p) for p in next_pred_state])
                E_next_simplified = simplify_formula_without_math(E_next)
                E_effects.extend([conjunct(E_now_simplified, X(E_next_simplified))])
            pred_effects.extend([conjunct(conjunct_formula_set(E), disjunct_formula_set(E_effects))])

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
                E_now_simplified = cnf_safe(E_now_simplified)

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

    _env_transition_ltl = [(G(implies(conjunct(conjunct(neg(init_state), env), src), disjunct_formula_set(env_transition_ltl[src])))) for src in
                           env_transition_ltl.keys()]
    _con_transition_ltl = [(G((implies(conjunct(conjunct(neg(init_state), con), src), disjunct_formula_set(con_transition_ltl[src]))))) for src in
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
                         effects_abstraction: EffectsAbstraction,
                         separate_by_effects: bool = False):
    ltl_abstraction = (
        to_env_con_separate_ltl_organised_by_pred_effects(effects_abstraction)
        if separate_by_effects
        else to_env_con_separate_ltl(effects_abstraction))

    predicate_vars = set(effects_abstraction.var_relabellings.values())

    program = effects_abstraction.get_program()
    pred_props = [Variable(s) for s in program.states] \
                 + list(predicate_vars) \
                 + [env, init_state]

    loop_vars = []
    for ltl_constraint in effects_abstraction.ranking_constraints:
        all_preds = atomic_predicates(ltl_constraint)
        loop_vars.extend([v for v in all_preds if isinstance(v, Variable)])

    pred_props.extend(list(set(loop_vars)))
    pred_props = list(set(pred_props))

    turn_logic = [init_state, G(X(neg(init_state))), env, G(iff(env, X(con)))]

    original_assumptions_expanded = [expand_ltl_to_env_con_steps(a, original_LTL_problem.env_props)
                                     for a in original_LTL_problem.assumptions]

    original_guarantees_expanded = [expand_ltl_to_env_con_steps(g, original_LTL_problem.env_props)
                                    for g in original_LTL_problem.guarantees]

    assumptions = turn_logic + effects_abstraction.ranking_constraints + ltl_abstraction + original_assumptions_expanded
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
    if isinstance(formula, Value) or isinstance(formula, MathExpr):
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
