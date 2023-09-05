import logging
import re
import time

from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from programs.abstraction.interface.predicate_abstraction import PredicateAbstraction
from programs.analysis.ranker import Ranker
from programs.typed_valuation import TypedValuation
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import get_differently_value_vars, function_is_of_natural_type, add_prev_suffix, \
    reduce_up_to_iff, ground_transitions, ground_predicate_on_vars, keep_bool_preds
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import conjunct, conjunct_formula_set, neg, true, is_boolean, dnf_safe, infinite_type, type_constraints, \
    is_tautology, related_to, equivalent, sat
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()


def try_liveness_refinement(counterstrategy_states: [str],
                            program: Program,
                            predicate_abstraction: PredicateAbstraction,
                            agreed_on_transitions,
                            disagreed_on_state,
                            ranking_invars: dict[Formula, [Formula]],
                            allow_user_input):
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
    ranking, invars, sufficient_entry_condition, exit_predicate = \
        liveness_step(program, loop, symbol_table,
                      entry_valuation, entry_predicate,
                      exit_condition,
                      exit_trans_state)

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

    # check if the ranking function is both increased in the loop
    inappropriate_rankings = []
    for ranking in new_ranking_invars.keys():
        for t, _ in loop:
            action_formula = conjunct_formula_set([BiOp(a.left, "==", add_prev_suffix(a.right)) for a in t.action])
            ranking_increase_with_action = conjunct(BiOp(ranking, ">", add_prev_suffix(ranking)),action_formula)
            if sat(ranking_increase_with_action, symbol_table):
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
        if not function_is_of_natural_type(ranking, invars, symbol_table):
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

seen_loops_cache = {}

def liveness_refinement(symbol_table,
                        program,
                        entry_condition,
                        unfolded_loop: [Transition],
                        exit_predicate_grounded,
                        add_natural_conditions=True):
    try:
        c_code = loop_to_c(symbol_table, program, entry_condition, unfolded_loop,
                           exit_predicate_grounded, add_natural_conditions)
        logging.info(c_code)

        if c_code in seen_loops_cache.keys():
            logging.info("Loop already seen..")
            return seen_loops_cache[c_code]

        ranker = Ranker()
        ranking_function, invars = ranker.check(c_code)
        seen_loops_cache[c_code] = (ranking_function, invars)

        return ranking_function, invars
    except Exception as e:
        raise e


def loop_to_c(symbol_table, program: Program, entry_condition: Formula, loop_before_exit: [Transition],
              exit_cond: Formula, add_natural_conditions=True):
    # params
    params = list(set(symbol_table[str(v)].type + " " + str(v)
                      for v in {v.name for v in program.valuation} | set(entry_condition.variablesin())
                      if
                      not is_boolean(v, program.valuation) and [str(vv) for t in loop_before_exit for vv in
                                                                (t.condition.variablesin()
                                                                 + entry_condition.variablesin()
                                                                 + exit_cond.variablesin()
                                                                 + [act.left for act in t.action]
                                                                 + [a for act in t.action for a in
                                                                    act.right.variablesin()])]))
    param_list = ", ".join(params)
    param_list = param_list.replace("integer", "int") \
        .replace("natural", "int") \
        .replace("nat", "int") \
        .replace("real", "double")

    natural_conditions = [v.split(" ")[1] + " >= 0 " for v in params if
                          not v.endswith("_prev") and symbol_table[v.split(" ")[1]].type in ["natural",
                                                                                             "nat"]]
    if add_natural_conditions:
        init = ["if(!(" + " && ".join(natural_conditions) + ")) return;" if len(natural_conditions) > 0 else ""]
    else:
        init = []
    choices = []

    for t in loop_before_exit:
        safety = str(type_constraints(t.condition, symbol_table))\
                        .replace(" = ", " == ")\
                        .replace(" & ", " && ")\
                        .replace(" | ", " || ")
        cond_simpl = str(t.condition.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ")
        acts = "\n\t\t".join([str(act.left) + " = " + str(act.right) + ";" for act in t.action if
                              not is_boolean(act.left, program.valuation) if act.left != act.right])

        if isinstance(string_to_prop(cond_simpl).simplify(), Value):
            if string_to_prop(cond_simpl).simplify().is_false():
                choices += ["break;"]
            elif string_to_prop(cond_simpl).simplify().is_true():
                choices += ["\t" + acts]
        else:
            # choices += ["\tif(" + cond_simpl + ") {" + acts + "}\n\t\t else break;"]
            choices += ["\t" + acts + ""]
        if safety != "true":
            if "..." in safety:
                raise Exception("Error: The loop contains a transition with a condition that is not a formula.")
            # choices += ["\tif(!(" + safety + ")) break;"]

    exit_cond_simplified = str(exit_cond.simplify()) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")
    exit_cond_var_constraints = str(type_constraints(exit_cond, symbol_table)) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")

    # TODO check for satisfiability instead of equality of with true
    loop_code = "\n\t\twhile(!(" + exit_cond_simplified + ")){\n\t" \
                + "\n\t\t\t".join(choices) \
                + "\n\t\t}\n"

    entry_cond_simplified = str(entry_condition.simplify())
    if entry_cond_simplified.lower() != "true":
        loop_code = "\n\tif(" + entry_cond_simplified\
                                    .replace(" = ", " == ")\
                                    .replace(" & ", " && ")\
                                    .replace(" | ", " || ") \
                            + "){" + loop_code + "\n\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init).strip() + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement_state(env_con_ce: [dict], last_cs_state, disagreed_on_state_dict, symbol_table):
    ce_with_stutter_states = []
    env_turn = True
    new_i_to_old_i = {}
    i = 0
    old_i = 0
    while i < len(env_con_ce):
        if env_turn:
            env_turn = False
            if env_con_ce[i]["turn"] == "env":
                ce_with_stutter_states.append((i, env_con_ce[i]))
                new_i_to_old_i[i] = old_i
            else:
                env_copy = env_con_ce[max(0, i - 1)]
                env_copy["turn"] = "env"
                ce_with_stutter_states.append((i + 1, env_con_ce[max(0, i - 1)]))
                new_i_to_old_i[old_i] = max(0, i - 1)
        else:
            env_turn = True
            if env_con_ce[i]["turn"] == "con":
                ce_with_stutter_states.append((i, env_con_ce[i]))
                new_i_to_old_i[i] = old_i
            else:
                con_copy = env_con_ce[max(0, i - 1)]
                con_copy["turn"] = "con"
                ce_with_stutter_states.append((i + 1, env_con_ce[max(0, i - 1)]))
                new_i_to_old_i[old_i] = max(0, i - 1)
        i += 1
        old_i += 1

    ce_with_stutter_states.append((len(env_con_ce), disagreed_on_state_dict))

    previous_visits = [i for i, dict in (ce_with_stutter_states) for key, value in dict.items()
                       if key == last_cs_state and value == "TRUE"]
    if len(previous_visits) - 1 > 0:  # ignoring last visit
        var_differences = []

        for i, visit in enumerate(previous_visits[:-1]):
            corresponding_ce_state = [ce_with_stutter_states[i][1] for i in range(visit, previous_visits[i + 1] + 1)]

            any_var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                               for i in range(0, len(corresponding_ce_state) - 1)]
            any_var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in any_var_differences]
            any_var_differences = [[v for v in vs if v in symbol_table.keys() and not str(v).endswith("_prev")] for vs in any_var_differences]
            any_var_differences = [[] != [v for v in vs if
                                      not re.match("(bool(ean)?)", symbol_table[v].type)] for vs in
                                      # the below only identifies loops when there are changes in infinite-domain variables in the loop
                                      # re.match("(int(eger)?|nat(ural)?|real|rational)", symbol_table[v].type)] for vs in
                               any_var_differences]
            if True in any_var_differences:
                var_differences += [True]
            else:
                var_differences += [False]

        if True in var_differences:
            # index_of_first_loop_entry = var_differences.index(True)
            # first_index = new_i_to_old_i[previous_visits[index_of_first_loop_entry]]
            index_of_last_loop_entry = len(var_differences) - 1 - var_differences[::-1].index(True)
            first_index = new_i_to_old_i[previous_visits[index_of_last_loop_entry]]
            return True, first_index
        else:
            return False, None
    else:
        return False, None


def use_liveness_refinement_trans(ce: [dict], symbol_table):
    counterstrategy_trans_con = []

    for i, state in enumerate(ce):
        if ce[i]["turn"] == "con":
            true_guards = [k.replace("counterstrategy_guard_", "") for k in ce[i].keys()
                           if k.startswith("counterstrategy_guard_")
                           and ce[i][k] == "TRUE"]
            true_acts = [k.replace("counterstrategy_act_", "") for k in ce[i].keys()
                         if k.startswith("counterstrategy_act_")
                         and ce[i][k] == "TRUE"]
            trans = [i for i in true_guards if i in true_acts]
            counterstrategy_trans_con += [set(trans)]
        elif i == len(ce) - 1:
            true_guards = [k.replace("counterstrategy_guard_", "") for k in ce[i].keys()
                           if k.startswith("counterstrategy_guard_")
                           and ce[i][k] == "TRUE"]
            counterstrategy_trans_con += [set(true_guards)]

    last_trans = counterstrategy_trans_con[-1]
    if any(x for x in last_trans if any(y for y in counterstrategy_trans_con[:-1] if x in y)):
        indices_of_visits = [i for i, x in enumerate(counterstrategy_trans_con) if
                             any(i for i in last_trans if i in x)]
        corresponding_ce_state = [ce[i] for i in
                                  range((3 * min(*indices_of_visits)) + 1, (3 * max(*indices_of_visits)) + 1)]  #
        var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                           for i in range(0, len(corresponding_ce_state) - 1)]
        var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in var_differences]
        var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in var_differences]
        if any([x for xs in var_differences for x in xs if
                re.match("(int(eger)?|nat(ural)?|real)", symbol_table[x].type)]):

            if len(indices_of_visits) == 0:
                raise Exception("Something weird here.")

            first_index = indices_of_visits[0]

            return True, first_index
        else:
            return False, None
    else:
        return False, None


def use_fairness_refinement(predicate_abstraction: PredicateAbstraction,
                            agreed_on_transitions,
                            disagreed_on_state,
                            last_counterstrategy_state,
                            symbol_table):
    yes = False
    mon_transitions = [(y, st) for (y, st) in agreed_on_transitions]
    ce = [x for _, x in agreed_on_transitions]

    # TODO we can do more analysis here
    # check first if there are actions that change the value of a variable
    if not any(a for t, _ in mon_transitions for a in t.action if not isinstance(a.right, Value)
                                                                  and a.left != a.right
                                                                  and not symbol_table[str(a.left)] == "bool"):
        return False, None, None, None, None

    yes_state, first_index_state = use_liveness_refinement_state(ce,
                                                                 last_counterstrategy_state,
                                                                 disagreed_on_state[1],
                                                                 symbol_table)
    if yes_state:
        first_index = first_index_state
        ce_prog_loop_tran_concretised = mon_transitions[first_index:]
        # prune up to predicate mismatch
        # TODO THIS IS NOT CORRECT
        # ce_prog_loop_tran_concretised = []
        pred_mismatch = False
        exit = False
        program = predicate_abstraction.get_program()

        # TODO simplify loop by finding repeated sequences
        if [] == [t for t, _ in ce_prog_loop_tran_concretised if [] != [a for a in t.action if infinite_type(a.left, program.valuation)]]:
            return False, None, None, None, None

        entry_valuation = conjunct_formula_set([BiOp(Variable(key), "=", Value(value))
                                                    for tv in program.valuation
                                                    for key, value in ce_prog_loop_tran_concretised[0][1].items()
                                                    if key == tv.name])

        all_state_preds = predicate_abstraction.get_state_predicates()

        true_preds = [p for p in all_state_preds if smt_checker.check(And(*conjunct(p, entry_valuation).to_smt(symbol_table)))]
        false_preds = [neg(p) for p in all_state_preds if p not in true_preds]
        entry_predicate = conjunct_formula_set(true_preds + false_preds)

        return True, ce_prog_loop_tran_concretised, entry_valuation, entry_predicate, pred_mismatch
    else:
        return False, None, None, None, None


def liveness_step(program, counterexample_loop, symbol_table, entry_valuation, entry_predicate,
                  exit_condition, exit_prestate):
    # ground transitions in the counterexample loop
    # on the environment and controller events in the counterexample\

    start = time.time()
    invars = []
    # TODO consider if sometimes bool vals are needed or not
    bool_vars = [v for v in symbol_table.keys() if symbol_table[v].type == "bool" or symbol_table[v].type == "boolean"]
    bool_vars += [Variable(str(v) + "_prev") for v in symbol_table.keys()]

    # first ground on bool vars

    entry_valuation_grounded = ground_predicate_on_vars(program, entry_valuation,
                                                        counterexample_loop[0][1], bool_vars, symbol_table).simplify()
    entry_predicate_grounded = ground_predicate_on_vars(program,
                                                        entry_predicate,
                                                        counterexample_loop[0][1], bool_vars, symbol_table).simplify()

    exit_predicate_grounded = ground_predicate_on_vars(program, exit_condition,
                                                       exit_prestate, bool_vars, symbol_table).simplify()
    dnf_exit_pred = dnf_safe(exit_predicate_grounded, symbol_table, simplify=True)
    disjuncts_in_exit_pred = [dnf_exit_pred] if not isinstance(dnf_exit_pred, BiOp) or not dnf_exit_pred.op.startswith(
        "|") else dnf_exit_pred.sub_formulas_up_to_associativity()

    if isinstance(exit_predicate_grounded, Value) or \
            is_tautology(exit_predicate_grounded, symbol_table, smt_checker):
        # in this case the exit is really happening before the last transition
        # TODO this shouldn't be happening, we should be identifying the real exit transition/condition
        loop_before_exit = ground_transitions(program, counterexample_loop, bool_vars, symbol_table)
        irrelevant_vars = []
        disjuncts_in_exit_pred_grounded = disjuncts_in_exit_pred
    else:
        # then discover which variables are related to the variables updated in the loop
        # TODO may also need to look at the guards of the transitions in the loop
        updated_in_loop_vars = [str(act.left) for t, _ in counterexample_loop for act in t.action if
                                act.left != act.right]

        relevant_vars = [str(v) for f in disjuncts_in_exit_pred for v in f.variablesin() if
                         any(v for v in f.variablesin() if str(v) in updated_in_loop_vars)]
        irrelevant_vars = [v for v in symbol_table.keys() if v not in relevant_vars]

        entry_predicate_grounded = ground_predicate_on_vars(program,
                                                            entry_predicate_grounded,
                                                            counterexample_loop[0][1], irrelevant_vars,
                                                            symbol_table).simplify()

        disjuncts_in_exit_pred_grounded = [ground_predicate_on_vars(program, e,
                                                                    exit_prestate, irrelevant_vars,
                                                                    symbol_table).simplify() for e in
                                           disjuncts_in_exit_pred]

        loop_before_exit = ground_transitions(program, counterexample_loop, irrelevant_vars + bool_vars, symbol_table)

    logging.info("first preprocessing for fairness refinement took " + str(time.time() - start))

    sufficient_entry_condition = None

    conditions = [(true(), True), (entry_predicate_grounded.simplify(), True), (entry_valuation_grounded, False)]

    ranking = None
    for (cond, add_natural_conditions) in conditions:
        for exit_pred in disjuncts_in_exit_pred_grounded:
            if len(exit_pred.variablesin()) == 0:
                continue
            try:
                ranking, invars = liveness_refinement(symbol_table,
                                                      program,
                                                      cond,
                                                      loop_before_exit,
                                                      exit_pred,
                                                      add_natural_conditions)
                if ranking is None:
                    continue
                sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                break
            except:
                continue

        if ranking is None:
            continue

        break

    if ranking is not None:
        # analyse ranking function for suitability and re-try
        if not isinstance(exit_predicate_grounded, Value) or \
                is_tautology(exit_predicate_grounded, symbol_table, smt_checker):
            start = time.time()
            # for each variable in ranking function, check if they are related in the exit condition, or transitively so
            updated_in_loop_vars = [str(act.left) for t in loop_before_exit for act in t.action if
                                    act.left != act.right]

            vars_in_ranking = ranking.variablesin()  # + [Variable(v) for v in updated_in_loop_vars]

            dnf_exit_pred = dnf_safe(exit_predicate_grounded, symbol_table)
            disjuncts_in_exit_pred = [dnf_exit_pred] if not isinstance(dnf_exit_pred,
                                                                       BiOp) or not dnf_exit_pred.op.startswith(
                "&") else dnf_exit_pred.sub_formulas_up_to_associativity()

            # compute related
            related_dict = {v: set() for v in (vars_in_ranking + [Variable(v) for v in updated_in_loop_vars])}
            for disjunct in disjuncts_in_exit_pred:
                for v in (vars_in_ranking + [Variable(v) for v in updated_in_loop_vars]):
                    related_dict[v] |= related_to(v, disjunct)

            # check if the ranking function relates variables that are related in entry condition
            if [] != [v for v in vars_in_ranking if v not in related_dict[vars_in_ranking[0]]]:
                logging.info(
                    "The ranking function discovered does not relate variables that are related in the exit condition.")
                all_updated_vars_mentioned_in_ranking = {v for v in vars_in_ranking if str(v) in updated_in_loop_vars}
                logging.info("Refining the loop code to focus on: " + ", ".join(
                    [str(v) for v in all_updated_vars_mentioned_in_ranking]) + "...")
                all_extra_vars = [v for v in vars_in_ranking
                                  if not any(v in related_dict[vv] for vv in all_updated_vars_mentioned_in_ranking)]

                # ground on these extra vars
                entry_valuation_grounded = ground_predicate_on_vars(program, entry_valuation,
                                                                    counterexample_loop[0][1], all_extra_vars,
                                                                    symbol_table).simplify()

                entry_predicate_grounded = ground_predicate_on_vars(program,
                                                                    entry_predicate_grounded,
                                                                    counterexample_loop[0][1], all_extra_vars,
                                                                    symbol_table).simplify()

                disjuncts_in_exit_pred_grounded = [ground_predicate_on_vars(program, e,
                                                                            exit_prestate, all_extra_vars,
                                                                            symbol_table).simplify() for e in
                                                   disjuncts_in_exit_pred_grounded]

                loop_before_exit = ground_transitions(program, counterexample_loop,
                                                      irrelevant_vars + bool_vars + all_extra_vars,
                                                      symbol_table)

                conditions = [(true(), True),
                              (entry_predicate_grounded.simplify(), True),
                              (entry_valuation_grounded, False)]

                ranking = None
                logging.info("second preprocessing for fairness refinement took " + str(time.time() - start))

                for (cond, add_natural_conditions) in conditions:
                    for exit_pred in disjuncts_in_exit_pred_grounded:
                        if len(exit_pred.variablesin()) == 0:
                            continue
                        try:
                            ranking, invars = liveness_refinement(symbol_table,
                                                                  program,
                                                                  cond,
                                                                  loop_before_exit,
                                                                  exit_pred,
                                                                  add_natural_conditions)
                            if ranking is None:
                                continue
                            sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                            break
                        except:
                            continue

                    if ranking is None:
                        continue
                    sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                    break

        if not smt_checker.check(And(*neg(exit_predicate_grounded).to_smt(symbol_table))):
            for grounded_t in loop_before_exit:
                if smt_checker.check(And(*neg(grounded_t.condition).to_smt(symbol_table))):
                    exit_predicate_grounded = neg(grounded_t.condition.simplify())
                    break
        return ranking, invars, sufficient_entry_condition, exit_predicate_grounded
    else:
        return None, None, None, None


def interactive_transition_predicates(existing_rankings: dict[Formula, [Formula]],
                                      symbol_table):
    finished = False
    new_rankings = []
    while not finished:
        try:
            text = input("Any suggestions of ranking function?")
            if text == "":
                break
            ranking = string_to_math_expression(text)
            text = input("Any suggestions of invariants?")

            if text == "":
                invars = []
            else:
                invars = list(map(string_to_math_expression, text.split(",")))
            if ranking in existing_rankings.keys():
                if equivalent(existing_rankings[ranking], conjunct_formula_set(invars)):
                    logging.info("This ranking function with the given invariants is already in use.")
                    continue
            new_rankings.append((ranking, invars))
        except Exception as e:
            pass

    new_ranking_invars = {}
    for (ranking, invars) in new_rankings:
        new_ranking_invars[ranking] = invars

        if not function_is_of_natural_type(ranking, invars, symbol_table):
            wellfounded_invar = MathExpr(BiOp(ranking, ">=", Value(0)))
            new_ranking_invars[ranking].append(wellfounded_invar)

    return new_ranking_invars