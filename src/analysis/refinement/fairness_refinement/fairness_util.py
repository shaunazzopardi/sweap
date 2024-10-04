import itertools
import logging
import time

from config import Config
from pysmt.shortcuts import Implies, And, Exists, Symbol, ForAll
from pysmt.typing import INT

from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.refinement.fairness_refinement.ranking_refinement import (use_fairness_refinement, find_ranking_function,
                                                                        ranking_refinement)
from analysis.refinement.fairness_refinement.structural_refinement import structural_refinement
from analysis.smt_checker import quantifier_elimination
from programs.program import Program
from programs.transition import Transition
from programs.util import add_prev_suffix, ground_predicate_on_vars
from prop_lang.biop import BiOp
from prop_lang.util import neg, conjunct_formula_set, conjunct, sat, true, resolve_implications, math_exprs_in_formula
from synthesis.mealy_machine import MealyMachine


def try_liveness_refinement(Cs: MealyMachine,
                            program: Program,
                            predicate_abstraction: PredicateAbstraction,
                            agreed_on_execution,
                            disagreed_on_state,
                            loop_counter,
                            allow_user_input):
    conf = Config.getConfig()

    if conf.only_safety:
        return False, None

    symbol_table = predicate_abstraction.get_symbol_table()
    ## check if should use fairness refinement or not
    start = time.time()
    use_fairness_refinement_flag, counterexample_loop, entry_valuation, entry_predicate, pred_mismatch \
        = use_fairness_refinement(Cs,
                                  predicate_abstraction,
                                  agreed_on_execution,
                                  disagreed_on_state,
                                  symbol_table)
    logging.info("determining whether fairness refinement is appropriate took " + str(time.time() - start))

    if not use_fairness_refinement_flag:
        return False, None

    ## do fairness refinement
    loop = counterexample_loop

    # TODO this isn't the real exit trans, it's a good approximation for now, but it may be a just
    #  an explicit or implicit stutter transition
    exit_condition = neg(conjunct_formula_set([p for p in disagreed_on_state[0]]))
    known_math_exprs = math_exprs_in_formula(entry_predicate)
    new_entry_constraints = []
    for p in math_exprs_in_formula(exit_condition):
        if p not in known_math_exprs:
            if sat(conjunct(p, entry_valuation), symbol_table):
                new_entry_constraints.append(p)
            else:
                new_entry_constraints.append(neg(p))

    entry_predicate = conjunct_formula_set([entry_predicate] + new_entry_constraints)
    success, result = \
        liveness_step(program,
                      entry_valuation,
                      entry_predicate,
                      exit_condition,
                      loop,
                      loop_counter,
                      symbol_table)

    return success, result


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
    next_relevant = set(vars_relevant_to_exit)

    while len(next_relevant) > 0:
        vars_relevant_to_exit.update(next_relevant)
        next_relevant.clear()

        for acts in body:
            for act in acts:
                if act.left != act.right and act.left in vars_relevant_to_exit:
                    act_vars = set(act.right.variablesin() + [act.left])
                    next_relevant.update(act_vars)
        next_relevant.difference_update(vars_relevant_to_exit)

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
    conf = Config.getConfig()
    if any(v for v in exit_cond.variablesin() if "_prev" in str(v)):
        return False, (None, None)

    body = [t.action for t, _, _ in concrete_body]
    reduced, reduced_body, vars_relevant_to_exit = cones_of_influence_reduction(exit_cond, body)
    if len(reduced_body) == 0:
        return False, (None, None)

    irrelevant_vars = [v for v in program.local_vars if v not in vars_relevant_to_exit]
    irrelevant_vars += program.env_events
    irrelevant_vars += program.con_events
    irrelevant_vars += [v for v in program.local_vars if any(tv for tv in program.valuation if str(v) == tv.name and tv.type.lower().startswith("bool"))]

    init_valuation = concrete_body[0][1] | concrete_body[0][2]
    # remove booleans from loop
    pre_cond = (ground_predicate_on_vars(program,
                              pre_cond,
                              init_valuation, irrelevant_vars, symbol_table)
     .simplify())
    entry_valuation = (ground_predicate_on_vars(program,
                              entry_valuation,
                              init_valuation, irrelevant_vars, symbol_table)
     .simplify())
    exit_cond = (ground_predicate_on_vars(program,
                              exit_cond,
                              init_valuation, irrelevant_vars, symbol_table)
     .simplify())
    exit_cond = resolve_implications(exit_cond).simplify().to_nuxmv()

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
                                           init_valuation, irrelevant_vars, symbol_table)
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

    conf = Config.getConfig()
    for cond in conditions:
        # this avoids loops that are not entered
        if not sat(conjunct(cond, neg(exit_cond)), symbol_table):
            return False, (None, None)
        # for exit_pred in disjuncts_in_exit_pred_grounded:
        if len(exit_cond.variablesin()) == 0:
            continue

        success, output = find_ranking_function(symbol_table,
                                                program,
                                                cond,
                                                reduced_body_flattened,
                                                exit_cond,
                                                add_natural_conditions)
        if not success:
            continue
        elif output == "already seen":
            return False, (None, None)
        elif sufficient_entry_condition is None:
            sufficient_entry_condition = cond

        if (conf.prefer_ranking or conf.only_ranking) and output != None:
            ranking, invars = output
            # if function_is_ranking_function(ranking, invars, body, symbol_table):
            if ranking not in used_rankings:
                if function_has_well_ordered_range(ranking, invars, symbol_table):
                    # this is not enough, doesn t take into accound precondition
                    if function_decreases_in_loop_body(ranking, invars, body, symbol_table):
                        used_rankings.add(ranking)
                        tran_preds, cons = ranking_refinement(ranking, invars)
                        _, state_preds, constraint = cons[0]
                        return True, (((state_preds, tran_preds), {constraint}), None)

        if not conf.only_ranking:
            if conditions[-1] == cond:
                return False, (None, None)
            else:
                return True, (None, structural_refinement([(true(), t) for t in reduced_body], cond, exit_cond, counter, symbol_table))

    if sufficient_entry_condition == None:
        raise Exception("Bug: Not even concrete loop is terminating..")

    if not conf.only_ranking and sufficient_entry_condition != conditions[-1]:
        return True, (None, structural_refinement([(true(), t) for t in reduced_body], sufficient_entry_condition, exit_cond, counter, symbol_table))
    else:
        return False, (None, None)
