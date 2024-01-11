import itertools
import logging
import time

from config import prefer_ranking, only_structural, only_ranking, only_safety
from pysmt.shortcuts import Implies, And, Exists, Symbol, ForAll
from pysmt.typing import INT

from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.refinement.fairness_refinement.ranking_refinement import use_fairness_refinement, \
    interactive_transition_predicates, find_ranking_function, ranking_refinement
from analysis.refinement.fairness_refinement.structural_refinement import structural_refinement
from analysis.smt_checker import quantifier_elimination
from programs.program import Program
from programs.transition import Transition
from programs.util import add_prev_suffix, reduce_up_to_iff, ground_predicate_on_vars
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.util import neg, conjunct_formula_set, conjunct, sat, true
from prop_lang.value import Value


def try_liveness_refinement(counterstrategy_states: [str],
                            program: Program,
                            predicate_abstraction: PredicateAbstraction,
                            agreed_on_transitions,
                            disagreed_on_state,
                            loop_counter,
                            allow_user_input):
    if only_safety:
        return False, None

    symbol_table = predicate_abstraction.get_symbol_table()
    ## check if should use fairness refinement or not
    try:
        logging.info("Counterstrategy states before environment step: " + ", ".join(counterstrategy_states))
        last_counterstrategy_state = counterstrategy_states[-1]
        start = time.time()
        use_fairness_refinement_flag, counterexample_loop, entry_valuation, entry_predicate, pred_mismatch \
            = use_fairness_refinement(predicate_abstraction,
                                      agreed_on_transitions,
                                      disagreed_on_state,
                                      last_counterstrategy_state,
                                      symbol_table)
        logging.info("determining whether fairness refinement is appropriate took " + str(time.time() - start))
    except Exception as e:
        logging.info("WARNING: " + str(e))
        logging.info("I will try to use safety instead.")
        return False, None

    if not use_fairness_refinement_flag:
        return False, None

    ## do fairness refinement
    exit_trans_state = disagreed_on_state[1]
    loop = counterexample_loop

    # TODO this isn't the real exit trans, it's a good approximation for now, but it may be a just
    #  an explicit or implicit stutter transition
    exit_condition = neg(conjunct_formula_set([p for p in disagreed_on_state[0]]))

    success, result = \
        liveness_step(program,
                      entry_valuation,
                      entry_predicate,
                      exit_condition,
                      loop,
                      loop_counter,
                      symbol_table)

    if True:
        return success, result


    # TODO in some cases we can use ranking abstraction as before:
    #  -DONE if ranking function is a natural number
    #  -if ranking function does not decrease outside the loop
    #  -DONE if supporting invariant ensures ranking function is bounded below

    if ranking is None:
        logging.info("I could not find a ranking function.")
        if allow_user_input:
            new_ranking_invars = interactive_transition_predicates(ranking_invars, symbol_table)
        else:
            return False, None
    else:
        logging.info("Found ranking function: "
                     + str(ranking)
                     + (" with invariants: " + ", ".join(map(str, invars))
                        if len(invars) > 0
                        else ""))
        if allow_user_input:
            text = input("Use suggested ranking function (y/n)?").lower().strip()
            while text != "y" and text != "n":
                text = input("Use suggested ranking function (y/n)?")
                if text == "n":
                    new_ranking_invars = interactive_transition_predicates(ranking_invars, symbol_table)
                elif text == "y":
                    new_ranking_invars = {ranking: invars}
                    break
        else:
            new_ranking_invars = {ranking: invars}

    inappropriate_rankings = []
    for ranking in new_ranking_invars.keys():
        for t, _ in loop:
            action_formula = conjunct_formula_set([BiOp(a.left, "==", add_prev_suffix(a.right)) for a in t.action])
            ranking_decrease_or_stutter_with_action = conjunct(BiOp(ranking, "<=", add_prev_suffix(ranking)), action_formula)
            # if there is an action in the loop where the ranking function does not decrease or stay the same,
            #    then the ranking function will not help us out of the loop
            if not sat(ranking_decrease_or_stutter_with_action, symbol_table):
                inappropriate_rankings.append(ranking)

    for inappropriate_ranking in inappropriate_rankings:
        new_ranking_invars.pop(inappropriate_ranking)

    if len(new_ranking_invars) == 0:
        logging.info("The found ranking function/s is/are increased in the loop, and thus is/are not appropriate "
                     "for ranking refinement.")
        return False, (sufficient_entry_condition, exit_predicate)

    new_transition_predicates = []
    new_decs = []
    for (ranking, invars) in new_ranking_invars.items():
        # if not function_bounded_below_by_0(ranking, invars, symbol_table):
        if not function_has_well_ordered_range(ranking, invars, symbol_table):
            wellfounded_invar = MathExpr(BiOp(ranking, ">=", Value(0)))
            new_ranking_invars[ranking].append(wellfounded_invar)

        dec = BiOp(add_prev_suffix(ranking), ">", ranking)
        new_decs.append(dec)
        inc = BiOp(add_prev_suffix(ranking), "<", ranking)
        new_transition_predicates.extend([dec, inc])

    old_trans_preds_decs = [tp for tp in predicate_abstraction.get_transition_predicates() if tp.op == ">"]
    new_all_trans_preds_decs = reduce_up_to_iff(old_trans_preds_decs,
                                                old_trans_preds_decs + new_decs,
                                                symbol_table)

    if len(new_all_trans_preds_decs) == len(old_trans_preds_decs):
        logging.info("New transition predicates are equivalent to old ones.")
        return False, None

    return True, (new_ranking_invars, new_transition_predicates)


def function_has_well_ordered_range(f, invars, symbol_table):
    if invars is None:
        invars = []
    ff = add_prev_suffix(f)
    formula = BiOp(ff, "<", f)
    fnode, _ = formula.to_smt(symbol_table)
    _, type_conds_fnode = f.to_smt(symbol_table)
    invar_fnode, invar_cond_fnode = conjunct_formula_set(invars).to_smt(symbol_table)

    formula = Implies(And([type_conds_fnode, invar_cond_fnode]), And([fnode, invar_fnode]))
    exis_vars = [Symbol(str(v), INT) for v in ff.variablesin()]
    forall_vars = [Symbol(str(vv), INT) for vv in f.variablesin()]
    quant_formula = Exists(exis_vars,
                           ForAll(forall_vars, formula))
    qe = quantifier_elimination(quant_formula)
    return str(qe).lower() == "true"


def function_decreases_in_loop_body(f, invars, body: [[BiOp]], symbol_table):
    # TODO ensure each action set in body has an action for every variable in f and invars
    at_least_one_decrease = False
    for acts in body:
        # for act in acts:
        act_pred = conjunct_formula_set([BiOp(act.left, "=", add_prev_suffix(act.right)) for act in acts])
        formulas = [act_pred] + invars + [BiOp(add_prev_suffix(f), "<", f)]

        if sat(conjunct_formula_set(formulas), symbol_table):
            return False
        else:
            at_least_one_decrease = True

    return at_least_one_decrease


def function_is_ranking_function(f, invars, body, symbol_table):
    return (function_has_well_ordered_range(f, invars, symbol_table) and
            function_decreases_in_loop_body(f, invars, body, symbol_table))


def cones_of_influence_reduction(exit_cond, body):
    vars_relevant_to_exit = set(exit_cond.variablesin())
    next_relevant = set()

    while len(next_relevant) > 0:
        vars_relevant_to_exit.update(next_relevant)
        next_relevant.clear()

        for acts in body:
            for act in acts:
                if act.left != act.right and act.left in vars_relevant_to_exit:
                    act_vars = set(act.right.variablesin() + [act.left])
                    next_relevant.update(act_vars)

    reduced = False
    reduced_body = []
    for acts in body:
        reduced_acts = []
        for act in acts:
            if act.left != act.right and act.left in vars_relevant_to_exit:
                reduced_acts.append(act)
            else:
                reduced = True
        if len(reduced_acts) > 0:
            reduced_body.append(reduced_acts)

    return reduced, reduced_body, vars_relevant_to_exit


used_rankings = set()

def liveness_step(program,
                  # prefix,
                  entry_valuation,
                  pre_cond,
                  exit_cond,
                  concrete_body,
                  counter,
                  symbol_table):
    body = [t.action for t, _ in concrete_body]
    reduced, reduced_body, vars_relevant_to_exit = cones_of_influence_reduction(exit_cond, body)

    irrelevant_vars = [v for v in program.local_vars if v not in vars_relevant_to_exit]
    # remove booleans from loop
    pre_cond = (ground_predicate_on_vars(program,
                              pre_cond,
                              concrete_body[0][1], irrelevant_vars, symbol_table)
     .simplify())
    entry_valuation = (ground_predicate_on_vars(program,
                              entry_valuation,
                              concrete_body[0][1], irrelevant_vars, symbol_table)
     .simplify())

    # heuristical search for sufficient weaker precondition for termination
    sufficient_weaker_precondition = None
    conditions = []
    # 1. try TRUE
    conditions.append(true())
    # 2. try pre_cond (i.e. conjunction of preds and neg preds true before entry)
    cond = pre_cond.to_nuxmv()
    if cond not in conditions:
        conditions.append(cond)
    # 3. try entry guard (grounded on E and C)
    entry_guard = (ground_predicate_on_vars(program,
                                           concrete_body[0][0].condition,
                                           concrete_body[0][1], irrelevant_vars, symbol_table)
                   .simplify()).to_nuxmv()
    if entry_guard not in conditions:
        conditions.append(entry_guard)
    # 4. try pre_cond & entry_guard
    cond = conjunct(pre_cond, entry_guard).to_nuxmv()
    if cond not in conditions:
        conditions.append(cond)
    # 5. actual initial valuation
    if entry_valuation.to_nuxmv() not in conditions:
        conditions.append(entry_valuation)

    # 4. if the above all don t terminate, then failed to weaken loop

    ranking = None
    add_natural_conditions = True

    sufficient_entry_condition = None

    reduced_body_flattened = itertools.chain.from_iterable(reduced_body)
    reduced_body_flattened = [Transition("q0", true(), [a], [], "q0") for a in reduced_body_flattened]

    for cond in conditions:
        # for exit_pred in disjuncts_in_exit_pred_grounded:
        if len(exit_cond.variablesin()) == 0:
            continue
        try:
            success, output = find_ranking_function(symbol_table,
                                                    program,
                                                    cond,
                                                    reduced_body_flattened,
                                                    exit_cond,
                                                    add_natural_conditions)
            if not success:
                continue
            elif output == "already seen":
                return False, None
            elif sufficient_entry_condition is None:
                sufficient_entry_condition = cond

            if (prefer_ranking or only_ranking) and output != None:
                ranking, invars = output
                # if function_is_ranking_function(ranking, invars, body, symbol_table):
                if ranking not in used_rankings:
                    if function_has_well_ordered_range(ranking, invars, symbol_table):
                        # if function_decreases_in_loop_body(ranking, invars, body, symbol_table):
                        used_rankings.add(ranking)
                        return True, ranking_refinement(ranking, invars)
            elif only_structural and not only_ranking:
                if conditions[-1] == cond:
                    return False, None
                else:
                    return True, structural_refinement([(true(), t) for t in reduced_body], cond, exit_cond, counter)

        except Exception as e:
            print(str(e))
            continue
    if sufficient_entry_condition == None:
        raise Exception("Bug: Not even concrete loop is terminating..")

    if not only_ranking:
        return True, structural_refinement([(true(), t) for t in reduced_body], sufficient_entry_condition, exit_cond, counter)
    else:
        return False, None