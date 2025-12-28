import logging

from pysmt.shortcuts import And, ForAll, Implies

from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.smt_checker import quantifier_elimination, sequence_interpolant
from parsing.string_to_prop_logic import string_to_prop
from programs.program import Program
from programs.util import reduce_up_to_iff
from prop_lang.biop import BiOp
from prop_lang.types.types import typed_var_to_pysmt_type
from prop_lang.types.values import BoolAtoms
from prop_lang.util import (
    neg,
    conjunct_formula_set,
    fnode_to_formula,
    var_to_predicate,
    is_tautology,
    is_contradictory,
    atomic_predicates,
    normalise_pred_multiple_vars,
    sat,
    conjunct,
    simplify_formula_with_math,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


def safety_refinement_seq_int(
    program: Program,
    predicate_abstraction: EffectsAbstraction,
    agreed_on_transitions,
    disagreed_on_state,
    signatures,
    allow_user_input: bool,
):
    symbol_table = predicate_abstraction.get_symbol_table()
    new_symbol_table = {}

    add_actions = "_prev" in str(disagreed_on_state[0])

    if allow_user_input:
        new_state_preds = interactive_state_predicates()
    else:
        ith_vars = lambda i: {
            Variable(v): Variable(v + "_" + str(i))
            for v in symbol_table.keys()
            if "_prev" not in v
        } | {
            Variable(v): Variable(v.removesuffix("_prev") + "_" + str(i - 1))
            for v in symbol_table.keys()
            if "_prev" in v
        }

        if len(agreed_on_transitions) == 0:
            raise Exception("No agreed on transitions found in the counterexample.")

        for i, (tran, prog_state, cs_state) in enumerate(agreed_on_transitions):
            if i == 0:
                init_formula = [
                    BiOp(e, "=", Value(prog_state[str(e)])) for e in program.local_vars
                ]
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
                p_0 = conjunct_formula_set(ps + init_formula).replace_vars(ith_vars(0))

                act = tran.action
                us_0 = [
                    BiOp(
                        Variable(str(u.left) + "_1"),
                        "=",
                        u.right.replace_vars(ith_vars(0)),
                    )
                    for u in act
                ]
                g = tran.condition.replace_vars(
                    {
                        e: Value(cs_state[str(e)])
                        for e, _ in program.env_events + program.con_events
                    }
                )
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
                g = tran.condition.replace_vars(
                    {
                        Variable(str(e)): Value(cs_state[str(e)])
                        for e, _ in program.env_events + program.con_events
                    }
                )
                g_i = g.replace_vars(ith_vars(i))
                act = tran.action + [
                    BiOp(e, "=", Value(cs_state[str(e)])) for e in program.num_in_out
                ]
                #     [
                #     u.replace_vars(
                #         {e: Value(cs_state[str(e)]) for e in program.inp_out_puts}
                #     )
                #     for u in tran.action
                # ]
                us_i = [
                    BiOp(
                        Variable(str(u.left) + "_" + str(i + 1)),
                        "=",
                        u.right.replace_vars(ith_vars(i)),
                    )
                    for u in act
                ]
                u_i = conjunct_formula_set(us_i)

                formulas.append(conjunct_formula_set([p_i, g_i, u_i]))
            new_symbol_table.update(
                {key + "_" + str(i): value for key, value in symbol_table.items()}
            )

        p_last = conjunct_formula_set(disagreed_on_state[0]).replace_vars(
            ith_vars(i + 1)
        )
        formulas.append(p_last)
        new_symbol_table.update(
            {key + "_" + str(i + 1): value for key, value in symbol_table.items()}
        )

        formulas_fnode = [f.to_smt(new_symbol_table)[0] for f in formulas]

        new_state_preds_fnode = sequence_interpolant(formulas_fnode)

        reset_vars = {
            Variable(v + "_" + str(i)): Variable(v)
            for v in program.symbol_table.keys()
            for i in range(0, len(agreed_on_transitions) + 1)
        }

        old_state_predicates = predicate_abstraction.raw_state_predicates

        success = True

        if new_state_preds_fnode:
            new_state_preds = [
                fnode_to_formula(f).replace_vars(reset_vars)
                for f in new_state_preds_fnode
            ]
            new_state_preds = [
                p for ps in new_state_preds for p in atomic_predicates(ps)
            ]

            new_state_preds = normalise_and_filter_preds(
                old_state_predicates, new_state_preds, signatures, symbol_table
            )

            success = not predicates_known(
                old_state_predicates, new_state_preds, symbol_table
            )
        else:
            success = False

        if not success:
            new_state_preds = qe_refinement(
                formulas,
                old_state_predicates,
                reset_vars,
                predicate_abstraction.program.symbol_table,
                new_symbol_table,
            )
            new_state_preds = normalise_and_filter_preds(
                old_state_predicates, new_state_preds, signatures, symbol_table
            )

            if len(new_state_preds) == 0:
                raise Exception("No new state predicates identified.")

        signatures.add(sig)
        new_all_preds = new_state_preds | old_state_predicates
        new_all_preds = reduce_up_to_iff(
            old_state_predicates,
            new_all_preds,
            symbol_table,
        )  # TODO symbol_table needs to be updated with prevs

        # check_for_nondeterminism_last_step(program_actually_took[1], predicate_abstraction.py.program, True)
        # raise Exception("Could not find new state predicates..")

    logging.info(
        "Using: "
        + ", ".join(
            [
                str(p)
                for p in new_all_preds
                if p not in old_state_predicates and neg(p) not in old_state_predicates
            ]
        )
    )

    new_preds = {
        p
        for p in new_all_preds
        if p not in old_state_predicates and neg(p) not in old_state_predicates
    }
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


def qe_refinement(
    formulas, state_predicates, reset_vars, symbol_table, new_symbol_table
):
    new_state_preds = set()
    for i in range(0, len(formulas)):
        typed_vars = list(
            {
                typed_var_to_pysmt_type(str(v), new_symbol_table[str(v)])[0]
                for f in formulas
                for v in f.variablesin()
                if str(v).split("_")[-1] != str(i)
            }
        )
        left = conjunct_formula_set(formulas[0:-1])
        right = formulas[-1]
        LHS = And(*left.to_smt(new_symbol_table))
        RHS = And(*right.to_smt(new_symbol_table))
        formula = ForAll(typed_vars, Implies(LHS, RHS))
        qe = quantifier_elimination(formula)
        pos_f = fnode_to_formula(qe)
        preds_in_res = atomic_predicates(pos_f)

        RHS = And(*neg(right).to_smt(new_symbol_table))
        formula = ForAll(typed_vars, Implies(LHS, RHS))
        qe = quantifier_elimination(formula)
        neg_f = fnode_to_formula(qe)
        preds_in_res.update(atomic_predicates(neg_f))

        to_proj = {}
        for p in preds_in_res:
            if not sat(conjunct(p, left), new_symbol_table):
                to_proj[p] = Value(BoolAtoms.FALSE)
            # elif is_tautology(implies(left, p), new_symbol_table):
            #     to_proj[p] = Value(BoolAtoms.TRUE)
        new_pos_f = pos_f.replace_formulas(to_proj)
        new_pos_f = simplify_formula_with_math(new_pos_f, new_symbol_table)

        new_neg_f = neg_f.replace_formulas(to_proj)
        new_neg_f = simplify_formula_with_math(new_neg_f, new_symbol_table)

        new_state_preds.update(
            [p.replace_vars(reset_vars) for p in atomic_predicates(new_pos_f)]
        )
        new_state_preds.update(
            [p.replace_vars(reset_vars) for p in atomic_predicates(new_neg_f)]
        )

        # TODO these may not be the highest quality predicates
        #       e.g., a predicate state_var < input is probably better than input < 0
        if not predicates_known(
            state_predicates,
            new_state_preds,
            symbol_table,
        ):
            break
    return new_state_preds


def predicates_known(old_state_predicates, new_state_preds, symbol_table):
    new_all_preds = new_state_preds | old_state_predicates

    new_all_preds = reduce_up_to_iff(
        old_state_predicates,
        list(new_all_preds),
        symbol_table,
    )

    return len(new_all_preds) == len(set(old_state_predicates))


def normalise_and_filter_preds(
    old_state_predicates, new_state_preds, signatures, symbol_table
):
    normalised_state_preds = set()
    for p in new_state_preds:
        result = normalise_pred_multiple_vars(p, signatures, symbol_table)
        if isinstance(result, Variable):
            normalised_state_preds.add(result)
        else:
            sig, _, preds = result
            signatures.add(sig)
            normalised_state_preds.update(preds)

    fresh_state_preds = {
        x
        for x in normalised_state_preds
        if x not in old_state_predicates
        and not is_tautology(x, symbol_table)
        and not is_contradictory(x, symbol_table)
    }
    return fresh_state_preds
