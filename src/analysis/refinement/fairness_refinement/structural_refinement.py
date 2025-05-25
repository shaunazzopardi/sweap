from programs.util import add_prev_suffix
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import (
    disjunct_formula_set,
    G,
    conjunct_formula_set,
    implies,
    neg,
    conjunct,
    X,
    iff,
    disjunct,
    F,
    atomic_predicates,
    sat,
    normalise_formula,
)
from prop_lang.variable import Variable


def structural_refinement(
    terminating_loop: [(Formula, [BiOp])],
    entry_condition: Formula,
    exit_condition: Formula,
    counter,
    signatures,
    symbol_table,
):
    print(
        "Structural Refinement: \nentry_cond:"
        + str(entry_condition)
        + "\nexit_cond:"
        + str(exit_condition)
        + "\nloop:"
        + ", ".join(map(str, [a for _, acts in terminating_loop for a in acts]))
    )
    ## TODO this will encode the loop
    # option 1: action-based encoding, however will miss sequence between con and env combined transitions,
    #           without new actions to combine them; would need an adhoc implementation for the effects abstraction,
    #           or modifying how we deal with transition predicates in the ltl abstraction

    # option 2: as the old one; transform the program to structurally separate the terminating loop from the rest of
    #           the program; would have the redo the predicate abstraction for all the previous predicates on the new
    #           program; or modify the abstraction to deal with predicates that can also talk about control states

    # TODO binary representation for in_loop vars
    in_loop_vars = [
        Variable("in_loop" + str(counter) + "_" + str(i))
        for i in range(0, len(terminating_loop))
    ]

    in_loop = disjunct_formula_set(in_loop_vars)

    entry_condition, entry_preds = normalise_formula(
        entry_condition, signatures, symbol_table
    )
    exit_condition, exit_preds = normalise_formula(
        exit_condition, signatures, symbol_table
    )

    atomic_state_preds = []
    atomic_tran_preds = []
    atomic_state_preds.extend(entry_preds)
    atomic_state_preds.extend(exit_preds)
    constraints = [neg(in_loop)]

    if len(in_loop_vars) > 1:
        only_one = G(
            conjunct_formula_set(
                [
                    implies(
                        v,
                        neg(
                            disjunct_formula_set([vv for vv in in_loop_vars if v != vv])
                        ),
                    )
                    for v in in_loop_vars
                ]
            )
        )

        constraints.append(only_one)

    stutters = []

    for i in range(0, len(terminating_loop)):
        # TODO: preds in guard need to be normalised
        guard, acts = terminating_loop[i]
        complete_acts = [
            BiOp(c, ":=", c)
            for c in exit_condition.variablesin()
            if not any(act for act in acts if act.left == c)
        ]
        complete_acts += acts

        acts_i = [
            BiOp(act.left, "=", add_prev_suffix(act.right)) for act in complete_acts
        ]
        act_i = conjunct_formula_set(acts_i)
        sts_i = [
            BiOp(act.left, "=", add_prev_suffix(act.left)) for act in complete_acts
        ]
        st_i = conjunct_formula_set(sts_i)

        atomic_state_preds.extend(atomic_predicates(guard))
        atomic_tran_preds.extend(acts_i)
        atomic_tran_preds.extend(sts_i)

        current_var = Variable("in_loop" + str(counter) + "_" + str(i))

        stutters.append(conjunct(st_i, current_var))

        if i == len(terminating_loop) - 1:
            next_var = Variable("in_loop" + str(counter) + "_0")
        else:
            next_var = Variable("in_loop" + str(counter) + "_" + str(i + 1))

        if i == 0:
            if not sat(
                conjunct_formula_set([entry_condition, neg(exit_condition), guard]),
                symbol_table,
            ):
                raise Exception(
                    str(
                        conjunct_formula_set(
                            [entry_condition, neg(exit_condition), guard]
                        )
                    )
                    + " is not satisfiable."
                )
            init = G(
                implies(
                    neg(in_loop),
                    iff(
                        conjunct_formula_set(
                            [
                                entry_condition,
                                neg(exit_condition),
                                guard,
                                X(act_i),
                            ]
                        ),
                        X(next_var),
                    ),
                )
            )
            constraints.append(init)

            if len(in_loop_vars) == 1:
                reenter = G(
                    implies(
                        conjunct_formula_set([current_var, neg(exit_condition), guard]),
                        X(iff(disjunct(act_i, st_i), next_var)),
                    )
                )
                constraints.append(reenter)

            else:
                reenter = G(
                    implies(
                        conjunct_formula_set([current_var, neg(exit_condition), guard]),
                        X(
                            conjunct_formula_set(
                                [
                                    implies(act_i, next_var),
                                    implies(st_i, current_var),
                                    iff(
                                        neg(disjunct(st_i, act_i)),
                                        neg(in_loop),
                                    ),
                                ]
                            )
                        ),
                    )
                )
                constraints.append(reenter)

            exit = G(
                implies(
                    conjunct_formula_set([current_var, (exit_condition)]),
                    X(neg(in_loop)),
                )
            )
            constraints.append(exit)

        if i != 0:
            constraint = G(
                implies(
                    conjunct_formula_set([current_var, guard]),
                    X(
                        conjunct_formula_set(
                            [
                                implies(act_i, next_var),
                                implies(st_i, current_var),
                                iff(neg(disjunct(st_i, act_i)), neg(in_loop)),
                            ]
                        )
                    ),
                )
            )

            constraints.append(constraint)

    fairness = disjunct(
        G(F(neg(in_loop))),
        disjunct_formula_set([F(G(stay)) for stay in stutters]),
    )
    constraints.append(fairness)

    return (set(atomic_state_preds + atomic_tran_preds), set()), set(constraints)
