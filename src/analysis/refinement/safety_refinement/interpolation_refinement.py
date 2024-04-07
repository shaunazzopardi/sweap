import logging

from pysmt.fnode import FNode
from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from analysis.smt_checker import binary_interpolant, sequence_interpolant
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import (ce_state_to_formula, ground_formula_on_ce_state_with_index, project_ce_state_onto_ev,
                           reduce_up_to_iff)
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import true, neg, conjunct_formula_set, conjunct, dnf_safe, fnode_to_formula, var_to_predicate
from prop_lang.value import Value
from prop_lang.variable import Variable

def safety_refinement_seq_int(program: Program,
                      predicate_abstraction: PredicateAbstraction,
                      agreed_on_transitions,
                      disagreed_on_state,
                      allow_user_input: bool,
                      keep_only_bool_interpolants: bool,
                      conservative_with_state_predicates: bool):
    symbol_table = predicate_abstraction.get_symbol_table()
    new_symbol_table = {}

    if allow_user_input:
        new_state_preds = interactive_state_predicates()
    else:
        ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys() if "_prev" not in v] + \
                              [BiOp(Variable(v), ":=", Variable(v.removesuffix("_prev") + "_" + str(i - 1))) for v in symbol_table.keys() if "_prev" in v]

        for i, (tran, prog_state, cs_state) in enumerate(agreed_on_transitions):
            if i == 0:
                init_formula = [BiOp(Variable(tv.name), "=", Value(tv.value)) for tv in program.valuation
                                                              if "_prev" not in tv.name]
                p_0 = conjunct_formula_set(init_formula).replace_vars(ith_vars(0))
                us_0 = [BiOp(Variable(str(u.left) + "_1"), "=", u.right.replace_vars(ith_vars(0))) for u in tran.action]
                g = tran.condition.replace_vars([BiOp(Variable(str(e)), ":=", Value(cs_state[str(e)])) for e in program.env_events + program.con_events])
                g_0 = g.replace_vars(ith_vars(0))
                u_0 = conjunct_formula_set(us_0)
                formulas = [conjunct_formula_set([p_0, g_0, u_0])]
            else:
                ps = []
                for k, v in cs_state.items():
                    if k.startswith("pred_"):
                        pred = var_to_predicate(k)
                        if v == "TRUE":
                            ps.append(pred)
                        else:
                            ps.append(neg(pred))
                p_i = conjunct_formula_set(ps).replace_vars(ith_vars(i))
                g = tran.condition.replace_vars([BiOp(Variable(str(e)), ":=", Value(cs_state[str(e)])) for e in program.env_events + program.con_events])
                g_i = g.replace_vars(ith_vars(i))
                us_i = [BiOp(Variable(str(u.left) + "_" + str(i + 1)), "=", u.right.replace_vars(ith_vars(i))) for u in tran.action]
                u_i = conjunct_formula_set(us_i)
                formulas.append(conjunct_formula_set([p_i, g_i, u_i]))
            new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

        p_last = conjunct_formula_set(disagreed_on_state[0]).replace_vars(ith_vars(i + 1))
        formulas.append(p_last)
        new_symbol_table.update({key + "_" + str(i + 1): value for key, value in symbol_table.items()})

        formulas_fnode = [f.to_smt(new_symbol_table)[0] for f in formulas]

        new_state_preds_fnode = sequence_interpolant(formulas_fnode)

        reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in program.symbol_table.keys() for i in
                      range(0, len(agreed_on_transitions) + 1)]

        new_state_preds = ([fnode_to_formula(f).replace_vars(reset_vars) for f in new_state_preds_fnode])
        new_state_preds = [p for ps in new_state_preds for p in ps.sub_formulas_up_to_associativity()]
        new_state_preds = list(set(new_state_preds))
        # if len(new_state_preds) == 0:
        #     logging.info("No state predicates identified.")
        #     if allow_user_input:
        #         new_state_preds = interactive_state_predicates()
        #     else:
        #         logging.info("I will try using the values of variables instead..")
        #         vars_mentioned_in_preds = {v for p in disagreed_on_state[0] for v in p.variablesin() if
        #                                    not str(v).endswith("_prev")}
        #         new_state_preds |= {BiOp(v, "=", Value(state[str(v)])) for v in vars_mentioned_in_preds for state
        #                             in [st for (_, st) in agreed_on_transitions + [disagreed_on_state]]}
        # else:
        #     logging.info("Found state predicates: " + ", ".join([str(p) for p in new_state_preds]))

    state_predicates = predicate_abstraction.get_state_predicates()
    new_all_preds = [x.simplify() for x in new_state_preds] + state_predicates

    new_all_preds = reduce_up_to_iff(predicate_abstraction.get_state_predicates(),
                                     list(new_all_preds),
                                     symbol_table
                                     | {str(v): TypedValuation(str(v),
                                                               symbol_table[str(v).removesuffix("_prev")].type,
                                                               "true")
                                        for p in new_all_preds
                                        for v in p.variablesin()
                                        if str(v).endswith(
                                             "prev")})  # TODO symbol_table needs to be updated with prevs

    if len(new_all_preds) < len(set(state_predicates)):
        raise Exception("There are somehow less state predicates than previously.")

    if len(set(new_all_preds)) == len(set(state_predicates)):
        new_state_preds = []
        for _, prog_state, _ in agreed_on_transitions:
            for v in program.local_vars:
                new_state_preds.append(BiOp(v, "=", Value(prog_state[str(v)])))
        new_all_preds = new_state_preds + state_predicates
        # check_for_nondeterminism_last_step(program_actually_took[1], predicate_abstraction.py.program, True)
        # raise Exception("Could not find new state predicates..")

    if keep_only_bool_interpolants:
        bool_interpolants = [p for p in new_state_preds if
                             p not in state_predicates and p in new_all_preds and 0 == len(
                                 [v for v in p.variablesin() if
                                  symbol_table[str(v)].type != "bool" and symbol_table[
                                      str(v)].type != "boolean"])]
        if len(bool_interpolants) > 0:
            new_all_preds = [p for p in new_all_preds if p in bool_interpolants or p in state_predicates]
    if conservative_with_state_predicates:
        # TODO some heuristics to choose state preds
        new_state_preds = [p for p in new_all_preds if p not in state_predicates]
        if len(new_state_preds) == 0:
            raise Exception("No new state predicates identified.")
        # get the number of variables associated with each predicates
        ordered_according_to_no_of_vars_used = [[p for p in new_state_preds if len(p.variablesin()) == n] for n in
                                                range(1, len(program.valuation) + 1)]
        ordered_according_to_no_of_vars_used = [ps for ps in ordered_according_to_no_of_vars_used if
                                                len(ps) > 0]
        new_all_preds = state_predicates + (ordered_according_to_no_of_vars_used[0] if len(
            ordered_according_to_no_of_vars_used) > 0 else [])

    logging.info("Using: " + ", ".join([str(p) for p in new_all_preds if p not in state_predicates and neg(p) not in state_predicates]))

    return True, {p for p in new_all_preds if p not in state_predicates and neg(p) not in state_predicates}


def interactive_state_predicates():
    finished = False
    new_preds = []
    while not finished:
        try:
            text = input("Any suggestions of state predicates?")
            if len(text.strip(" ")) == 0:
                finished = True
            else:
                new_preds = set(map(string_to_prop, text.split(",")))
                finished = True
        except Exception as e:
            pass
    return new_preds
