import logging

from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from parsing.string_to_prop_logic import string_to_prop
from analysis.smt_checker import sequence_interpolant
from programs.program import Program
from programs.typed_valuation import TypedValuation
from programs.util import reduce_up_to_iff
from prop_lang.biop import BiOp
from prop_lang.util import (neg, conjunct_formula_set, fnode_to_formula, var_to_predicate, is_tautology,
                            is_contradictory, atomic_predicates, normalise_pred_multiple_vars)
from prop_lang.value import Value
from prop_lang.variable import Variable

def safety_refinement_seq_int(program: Program,
                      predicate_abstraction: EffectsAbstraction,
                      agreed_on_transitions,
                      disagreed_on_state,
                      signatures,
                      allow_user_input: bool,
                      keep_only_bool_interpolants: bool,
                      conservative_with_state_predicates: bool,
                      enable_equality_to_le: bool=False):
    symbol_table = predicate_abstraction.get_symbol_table()
    new_symbol_table = {}

    add_actions = "_prev" in str(disagreed_on_state[0])

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
                        if not add_actions and "_prev" in str(pred):
                            continue
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

        if new_state_preds_fnode is None:
            raise Exception("Bug: Counterexample does not contain a sequence interpolant.")
        reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in program.symbol_table.keys() for i in
                      range(0, len(agreed_on_transitions) + 1)]

        new_state_preds = ([fnode_to_formula(f).replace_vars(reset_vars) for f in new_state_preds_fnode])
        new_state_preds = [p for ps in new_state_preds for p in atomic_predicates(ps)]
        new_state_preds = list(set(new_state_preds))
        new_state_preds = [x for x in new_state_preds if
                           not is_tautology(x, symbol_table) and not is_contradictory(x, symbol_table)]

    state_predicates = set()
    state_predicates.update(s.pred for s in predicate_abstraction.get_state_predicates())
    state_predicates.update(s for c in predicate_abstraction.v_to_chain_pred.values() for s in c.chain)
    # new_state_preds = list(itertools.chain.from_iterable(map(lambda x: x[1], map(normalise_predicate, new_state_preds))))
    normalised_state_preds = set()
    for p in new_state_preds:
        result = normalise_pred_multiple_vars(p, signatures, program.symbol_table)
        if len(result) == 1:
            normalised_state_preds.add(result)
        else:
            sig, _, preds = result
            signatures.add(sig)
            normalised_state_preds.update(preds)
    new_state_preds = normalised_state_preds
    new_all_preds = new_state_preds | state_predicates

    new_all_preds = reduce_up_to_iff(state_predicates,
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
        raise Exception("Did not find new state predicates.")
        # new_state_preds = set()
        # prog_states = [prog_state for _, prog_state, _ in agreed_on_transitions] + [disagreed_on_state[1][1]]
        # for prog_state in prog_states:
        #     for v in program.local_vars:
        #         if str(Value(prog_state[str(v)])).lower() == "true":
        #             new_state_preds.add(v)
        #         elif str(Value(prog_state[str(v)])).lower() == "false":
        #             new_state_preds.add(neg(v))
        #         else:
        #             pred = BiOp(v, "=", Value(prog_state[str(v)]))
        #             sig, _, preds = normalise_pred_multiple_vars(pred, signatures, symbol_table)
        #             new_state_preds.update(preds)
        #             signatures.add(sig)
        # new_all_preds = new_state_preds | state_predicates
        # new_all_preds = reduce_up_to_iff(state_predicates,
        #                                  new_all_preds,
        #                                  symbol_table
        #                                  | {str(v): TypedValuation(str(v),
        #                                                            symbol_table[str(v).removesuffix("_prev")].type,
        #                                                            "true")
        #                                     for p in new_all_preds
        #                                     for v in p.variablesin()
        #                                     if str(v).endswith(
        #                                          "prev")})  # TODO symbol_table needs to be updated with prevs

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

    new_preds = {p for p in new_all_preds if p not in state_predicates and neg(p) not in state_predicates}
    if len(new_preds) == 0:
        print("No new state predicates identified.")

    return True, new_preds


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
