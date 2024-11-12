import logging
import re
import time

from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.ranker import Ranker
from analysis.smt_checker import check
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import get_differently_value_vars, ground_predicate_on_vars, add_prev_suffix
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (conjunct, conjunct_formula_set, neg, is_boolean, type_constraints, is_tautology, sat,
                            atomic_predicates, disjunct, G, F, implies, iff, stringify_pred, var_to_predicate_alt,
                            strip_mathexpr, var_to_predicate)
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.moore_machine import MooreMachine

seen_loops_cache = {}


def already_an_equivalent_ranking(prev_decs, new_dec):
    for prev_dec in prev_decs:
        if new_dec == prev_dec:
            return True
        else:
            equiv = iff(prev_dec, new_dec)
            symbol_table = {str(v): TypedValuation(str(v), "int", None) for v in equiv.variablesin()}
            if is_tautology(equiv, symbol_table):
                return True
    return False


def ranking_refinement_both_sides(ranking, invar_pos, invar_neg):
    dec = BiOp(add_prev_suffix(ranking), ">", ranking)
    inc = BiOp(add_prev_suffix(ranking), "<", ranking)
    tran_preds = {dec, inc}

    constraints = []

    if len(invar_pos) > 0:
        inv = conjunct_formula_set(invar_pos)
        constraints += [(dec, atomic_predicates(inv), implies(G(F(dec)), G(F(disjunct(inc, neg(inv))))))]
    else:
        constraints += [(dec, set(), implies(G(F(dec)), G(F(inc))))]

    if len(invar_neg) > 0:
        inv = conjunct_formula_set(invar_neg)
        constraints += [(inc, atomic_predicates(inv), implies(G(F(inc)), G(F(disjunct(dec, neg(inv))))))]
    else:
        constraints += [(inc, set(), implies(G(F(inc)), G(F(dec))))]

    return tran_preds, constraints


def ranking_refinement(ranking, invars, there_is_inc=True):
    ranking = strip_mathexpr(ranking)
    if isinstance(ranking, BiOp):
        left = (ranking.left)
        right = (ranking.right)
        if ranking.op == "-":
            if isinstance(ranking.left, Value):
                dec = BiOp(right, ">", add_prev_suffix(right))
                inc = BiOp(right, "<", add_prev_suffix(right))
            elif isinstance(ranking.right, Value):
                dec = BiOp(left, "<", add_prev_suffix(left))
                inc = BiOp(left, ">", add_prev_suffix(left))
            else:
                sort = sorted([left, right], key=lambda x: str(x))
                if sort[0] == left:
                    dec = BiOp(ranking, "<", add_prev_suffix(ranking))
                    inc = BiOp(ranking, ">", add_prev_suffix(ranking))
                else:
                    new_ranking = BiOp(sort[0], "-", sort[1])
                    dec = BiOp(new_ranking, ">", add_prev_suffix(new_ranking))
                    inc = BiOp(new_ranking, "<", add_prev_suffix(new_ranking))
        elif ranking.op == "+":
            if isinstance(ranking.left, Value):
                dec = BiOp(right, "<", add_prev_suffix(right))
                inc = BiOp(right, ">", add_prev_suffix(right))
            elif isinstance(ranking.right, Value):
                dec = BiOp(left, "<", add_prev_suffix(left))
                inc = BiOp(left, ">", add_prev_suffix(left))
            else:
                sort = sorted([left, right], key=lambda x: str(x))
                new_ranking = BiOp(sort[0], "+", sort[1])
                inc = BiOp(new_ranking, ">", add_prev_suffix(new_ranking))
                dec = BiOp(new_ranking, "<", add_prev_suffix(new_ranking))
        else:
            inc = BiOp(ranking, ">", add_prev_suffix(ranking))
            dec = BiOp(ranking, "<", add_prev_suffix(ranking))
    else:
        inc = BiOp(ranking, ">", add_prev_suffix(ranking))
        dec = BiOp(ranking, "<", add_prev_suffix(ranking))

    if len(invars) > 0:
        inv = conjunct_formula_set(invars)
        state_preds = atomic_predicates(inv)
        if not there_is_inc:
            constraint = implies(G(F(dec)), G(F(neg(inv))))
            tran_preds = {dec}
        else:
            tran_preds = {dec, inc}
            constraint = implies(G(F(dec)), G(F(disjunct(inc, neg(inv)))))
    else:
        if there_is_inc:
            tran_preds = {dec, inc}
            constraint = implies(G(F(dec)), G(F(inc)))
            state_preds = set()
        else:
            return set(), []

    return tran_preds, state_preds, (dec, constraint)


def find_ranking_function(symbol_table,
                          program,
                          entry_condition,
                          unfolded_loop: [Transition],
                          exit_predicate_grounded,
                          add_natural_conditions=True):
    c_code = loop_to_c(symbol_table, program, entry_condition, unfolded_loop,
                       exit_predicate_grounded, add_natural_conditions)
    logging.info(c_code)

    if c_code in seen_loops_cache.keys():
        logging.info("Loop already seen..")
        return True, "already seen"

    ranker = Ranker()
    success, output = ranker.check(c_code)
    if success:
        if output is None:
            return success, None

        ranking_function, invars = output
        seen_loops_cache[c_code] = (ranking_function, invars)

    return success, output


def loop_to_nuxmv(symbol_table, program: Program, entry_condition: Formula, loop_before_exit: [Transition],
              exit_cond: Formula, add_natural_conditions=True):
    nuxmv = ["MODULE main"]
    nuxmv += ["VAR"]
    raise NotImplementedError("loop_to_nuxmv not implemented yet")


def loop_to_c(symbol_table, program: Program, entry_condition: Formula, loop_before_exit: [Transition],
              exit_cond: Formula, add_natural_conditions=True):
    type_constraints_str = []
    # params
    params = []
    for v in {v.name for v in program.valuation} | set(entry_condition.variablesin()):
        if is_boolean(v, program.valuation):
            continue

        relevant_vars = [str(vv) for t in loop_before_exit for vv in
                                                                (t.condition.variablesin()
                                                                 + entry_condition.variablesin()
                                                                 + exit_cond.variablesin()
                                                                 + [act.left for act in t.action]
                                                                 + [a for act in t.action for a in
                                                                    act.right.variablesin()])]
        if v not in relevant_vars:
            continue

        type = symbol_table[str(v)].type
        if type in ["natural", "nat"]:
            params.append("int " + str(v))
            type_constraints_str.append(str(v) + " >= 0 ")
        elif type in ["int", "integer"]:
            params.append("int " + str(v))
        elif re.match(r"-?[0-9]+\.\.-?[0-9]+", type):
            params.append("int " + str(v))
            lower, upper = type.split("..")[0:2]
            type_constraints_str.append(str(v) + " >= " + lower)
            type_constraints_str.append(str(v) + " <= " + upper)
        else:
            params.append(type + " " + str(v))

    param_list = ", ".join(params)

    natural_conditions = [v.split(" ")[1] + " >= 0 " for v in params if
                          not v.endswith("_prev") and symbol_table[v.split(" ")[1]].type in ["natural",
                                                                                             "nat"]]
    if add_natural_conditions:
        init = ["if(!(" + " && ".join(type_constraints_str) + ")) return;" if len(type_constraints_str) > 0 else ""]
    else:
        init = []
    choices = []

    for t in loop_before_exit:
        safety = str(type_constraints(t.condition, symbol_table)) \
            .replace(" = ", " == ") \
            .replace(" & ", " && ") \
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
    loop_code = "\n\twhile(!(" + exit_cond_simplified + ")){\n\t" \
                + "\n\t\t\t".join(choices) \
                + "\n\t}\n"

    entry_cond_simplified = str(entry_condition.simplify())
    if entry_cond_simplified.lower() != "true":
        loop_code = "\n\tif(" + entry_cond_simplified \
            .replace(" = ", " == ") \
            .replace(" & ", " && ") \
            .replace(" | ", " || ") \
                    + "){" + loop_code + "\n\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init).strip() + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement_state(ce: [dict], last_cs_state, disagreed_on_state_dict, symbol_table):
    new_ce = list(enumerate(ce + [disagreed_on_state_dict]))

    previous_visits = [i for i, dict in (new_ce) for key, value in dict.items()
                       if key == last_cs_state and value == "TRUE"]
    if len(previous_visits) - 1 > 0:  # ignoring last visit
        var_differences = []

        for i, visit in enumerate(previous_visits[:-1]):
            corresponding_ce_state = [new_ce[i][1] for i in range(visit, previous_visits[i + 1] + 1)]

            any_var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                                   for i in range(0, len(corresponding_ce_state) - 1)]
            any_var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in any_var_differences]
            any_var_differences = [[v for v in vs if v in symbol_table.keys() and not str(v).endswith("_prev")] for vs
                                   in any_var_differences]
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
            index_of_last_loop_entry = len(var_differences) - 1 - var_differences[::-1].index(True)
            first_index = new_ce[previous_visits[index_of_last_loop_entry]]
            return True, first_index[0]
        else:
            return False, None
    else:
        return False, None


def use_liveness_refinement_state_joined(Cs: MooreMachine,
                                         program,
                                         predicate_abstraction: PredicateAbstraction,
                                         ce: [dict],
                                         prog_trans,
                                         last_cs_state,
                                         disagreed_on_state_dict,
                                         symbol_table):
    # processing last_cs_state to ignore env behaviour
    tran_preds = [stringify_pred(t) for t in predicate_abstraction.get_transition_predicates()]
    tran_preds += [stringify_pred(t) for t in predicate_abstraction.get_state_predicates() if "_prev" in str(t)]
    # TODO do this better later
    inloop_vars = [Variable(k) for k in ce[0].keys() if k.startswith("in_loop")]
    irrelevant_vars = program.env_events + tran_preds + inloop_vars

    symbol_table_with_inloop_vars = symbol_table | {str(l): TypedValuation(str(l), "bool", None) for l in inloop_vars}

    last_props_state_dict = {str(p): disagreed_on_state_dict[str(p)]
                             for p in irrelevant_vars}

    last_pred_state = ground_predicate_on_vars(program,
                                               Cs.out[last_cs_state],
                                               last_props_state_dict,
                                               irrelevant_vars,
                                               symbol_table_with_inloop_vars)

    last_pred_state_wo_props = ground_predicate_on_vars(program,
                                                        last_pred_state,
                                                        last_props_state_dict,
                                                        irrelevant_vars,
                                                        symbol_table_with_inloop_vars)

    if all(str(v).startswith("bin_st") for v in last_pred_state.variablesin()):
        return False, None

    previous_visits = []
    for i, ce_state in enumerate(ce):
        cs_st = [str(st) for st in Cs.states if ce_state[str(st)] == "TRUE"][0]

        pred_state_wo_props = ground_predicate_on_vars(program,
                                                       Cs.out[cs_st],
                                                       ce_state,
                                                       irrelevant_vars,
                                                       symbol_table_with_inloop_vars)
        tran_cond = prog_trans[i][0].condition

        f = iff(pred_state_wo_props, last_pred_state_wo_props)
        if is_tautology(f.replace_formulas(lambda x: x if not isinstance(x, Variable) else var_to_predicate(x)), symbol_table_with_inloop_vars):
            if sat(conjunct(tran_cond, last_pred_state.replace_formulas(lambda x: x if not isinstance(x, Variable) else var_to_predicate(x))), symbol_table_with_inloop_vars):
                previous_visits.append(i)

    new_ce = list(enumerate(ce + [disagreed_on_state_dict]))
    previous_visits.append(len(ce))

    if len(previous_visits) - 1 > 0:  # ignoring last visit
        var_differences = []

        for i, visit in enumerate(previous_visits[:-1]):
            corresponding_ce_state = [new_ce[i][1] for i in range(visit, previous_visits[i + 1] + 1)]

            any_var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                                   for i in range(0, len(corresponding_ce_state) - 1)]
            any_var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in any_var_differences]
            any_var_differences = [[v for v in vs if v in symbol_table.keys() and not str(v).endswith("_prev")] for vs
                                   in any_var_differences]
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
            index_of_last_loop_entry = len(var_differences) - 1 - var_differences[::-1].index(True)
            first_index = new_ce[previous_visits[index_of_last_loop_entry]]
            return True, first_index[0]
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


def massage_ce(Cs: MooreMachine,
               agreed_on_transitions):
    # agreed_on_transitions is of form [t, st], st has the next Cs state, and current variable state
    init_cs_st = {Cs.init_st: "TRUE"}
    init_cs_st |= {s: "FALSE" for s in Cs.states if s != init_cs_st}

    new_agreed_on_transitions = []
    prev_cs_st = init_cs_st

    for t, st in agreed_on_transitions:
        new_st = prev_cs_st
        new_st |= {k: v for k, v in st.items() if k not in new_st.keys()}

        new_agreed_on_transitions.append((t, new_st))
        prev_cs_st = {k: v for k, v in st.items() if k in Cs.states}

    return new_agreed_on_transitions


def use_fairness_refinement(Cs: MooreMachine,
                            predicate_abstraction: PredicateAbstraction,
                            agreed_on_execution,
                            disagreed_on_state,
                            symbol_table):
    mon_transitions = agreed_on_execution
    ce = [prog_st | cs_st for _, prog_st, cs_st in mon_transitions]

    # TODO we can do more analysis here
    # check first if there are actions that change the value of a variable
    if not any(a for t, _, _ in mon_transitions for a in t.action if not isinstance(a.right, Value)
                                                                  and a.left != a.right
                                                                  and not symbol_table[str(a.left)] == "bool"):
        return False, None, None, None, None

    last_counterstrategy_state = [st for st, v in disagreed_on_state[1][2].items() if st in Cs.states and v == "TRUE"][0]
    yes_state, first_index_state = use_liveness_refinement_state(ce,
                                                                 last_counterstrategy_state,
                                                                 disagreed_on_state[1][1] | disagreed_on_state[1][2],
                                                                 symbol_table)
    if not yes_state:
        yes_state, first_index_state = use_liveness_refinement_state_joined(Cs,
                                                                            predicate_abstraction.get_program(),
                                                                            predicate_abstraction,
                                                                            ce,
                                                                            mon_transitions,
                                                                            last_counterstrategy_state,
                                                                            disagreed_on_state[1][1] | disagreed_on_state[1][
                                                                                 2],
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

        # # TODO simplify loop by finding repeated sequences
        # if [] == [t for t, _ in ce_prog_loop_tran_concretised if
        #           [] != [a for a in t.action if infinite_type(a.left, program.valuation)]]:
        #     return False, None, None, None, None

        entry_valuation = conjunct_formula_set([BiOp(Variable(key), "=", Value(value))
                                                for tv in program.valuation
                                                for key, value in ce_prog_loop_tran_concretised[0][1].items()
                                                if key == tv.name])

        all_state_preds = predicate_abstraction.get_state_predicates()


        true_preds = [p for p in all_state_preds if
                      check(And(*conjunct(p, entry_valuation).to_smt(symbol_table)))]
        false_preds = [neg(p) for p in all_state_preds if p not in true_preds]
        entry_predicate = conjunct_formula_set(true_preds + false_preds)

        return True, ce_prog_loop_tran_concretised, entry_valuation, entry_predicate, pred_mismatch
    else:
        return False, None, None, None, None
