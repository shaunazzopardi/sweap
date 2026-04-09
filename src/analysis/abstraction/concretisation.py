from pysmt.shortcuts import And

from analysis.smt_checker import check
from programs.util import (
    is_deterministic,
    stutter_transition,
    preds_in_state,
    transition_formula,
    add_prev_suffix,
)
from prop_lang.biop import BiOp
from prop_lang.util import (
    neg,
    conjunct_formula_set,
    disjunct_formula_set,
    propagate_negations,
    sat,
    simplify_formula_with_math,
    var_to_predicate,
    is_predicate_var,
    normalise_mathexpr,
    unsat_core,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


def _is_transition_like_predicate_formula(p):
    return any("_prev" in str(v) for v in p.variablesin())


def _is_initial_compat_phase(cs_state: dict[str, str]):
    return (
        cs_state.get("init_state") == "TRUE" or cs_state.get("second_state") == "TRUE"
    )


def _filter_preds_for_compat_state(preds, cs_state):
    # Transition predicates are intentionally not enforced during the initial
    # compatibility phase, so they must not be used to derive refinement facts.
    if _is_initial_compat_phase(cs_state):
        return [p for p in preds if not _is_transition_like_predicate_formula(p)]
    return preds


def concretize_transitions(program, indices_and_state_list, incompatible_state):
    transitions = program.transitions

    # ignore the mismatch state
    concretized = []

    for i in range(0, len(indices_and_state_list[0])):
        program_transition = indices_and_state_list[0][i]
        program_state = indices_and_state_list[1][i]
        cs_state = indices_and_state_list[2][i]

        if int(program_transition) != -1:
            concretized += [
                (transitions[int(program_transition)], program_state, cs_state)
            ]
        else:
            stutter_trans = stutter_transition(
                program,
                [q for q in program.states if program_state[str(q)] == "TRUE"][0],
            )
            if stutter_trans == None:
                raise Exception("stuttering transition not found")
            else:
                concretized += [(stutter_trans, program_state, cs_state)]

    # two options, either we stopped because of a state mismatch or a predicate mismatch
    incompatibility_formula = []
    if incompatible_state[2]["compatible_states"] == "FALSE":
        if program.deterministic is None:
            if not is_deterministic(program):
                raise Exception(
                    "Program is non-deterministic, concretisation of abstract counterexample may not work in this case."
                )
        elif not program.deterministic:
            raise Exception(
                "Program is non-deterministic, concretisation of abstract counterexample may not work in this case."
            )

        failed_condition = neg(concretized[-1][0].condition)
        reduced = failed_condition.replace(
            {
                Variable(str(v)): Value(concretized[-1][2][str(v)])
                for v, _ in program.env_events + program.con_events
            }
        )
        reduced_simplified = simplify_formula_with_math(reduced, program.symbol_table)
        reduced_normalised = reduced_simplified.replace_formulas(normalise_mathexpr)

        return concretized[:-1], ([reduced_normalised], concretized[-1])
    else:
        if (
            incompatible_state[2]["compatible_state_predicates"] == "FALSE"
            or incompatible_state[2]["compatible_tran_predicates"] == "FALSE"
        ):
            pred_state = _filter_preds_for_compat_state(
                [
                    p
                    for p in preds_in_state(incompatible_state[2])
                    if not any(v for v in p.variablesin() if v in program.inp_out_puts)
                ],
                incompatible_state[2],
            )
            predicate_state_before_incompatibility = _filter_preds_for_compat_state(
                [
                    add_prev_suffix(p)
                    for p in preds_in_state(concretized[-1][2])
                    if not any(v for v in p.variablesin() if "_prev" in str(v))
                ],
                concretized[-1][2],
            )
            # we check if this incompatible state formula is ever possibly true after the last transition
            # if it is then the problem is with the predicate state
            if sat(
                conjunct_formula_set(
                    pred_state
                    + predicate_state_before_incompatibility
                    + [transition_formula(concretized[-1][0])]
                ),
                program.symbol_table,
            ):
                # reduce predicate mismatch to the actually mismatched predicates
                for p in pred_state:
                    # TODO: here using (incompatible_state[1] | incompatible_state[2])
                    #       since program variable state may be split between them
                    #       instead of just incompatible_state[1], in error
                    #       this is a bandaid fix, should be fixed properly later
                    var_state = [
                        BiOp(
                            v,
                            "=",
                            Value(
                                (incompatible_state[1] | incompatible_state[2])[str(v)]
                            ),
                        )
                        for v in p.variablesin()
                    ]
                    if not sat(
                        conjunct_formula_set([p] + var_state),
                        program.symbol_table,
                    ):
                        incompatibility_formula.append(p)

                if len(incompatibility_formula) == 0:
                    for p in pred_state:
                        # TODO: here using (incompatible_state[1] | incompatible_state[2])
                        #       since program variable state may be split between them
                        #       instead of just incompatible_state[1], in error
                        #       this is a bandaid fix, should be fixed properly later
                        var_state = [
                            BiOp(
                                v,
                                "=",
                                Value(
                                    (incompatible_state[1] | incompatible_state[2])[
                                        str(v)
                                    ]
                                ),
                            )
                            for v in p.variablesin()
                        ]
                        if not sat(
                            conjunct_formula_set([p] + var_state),
                            program.symbol_table,
                        ):
                            incompatibility_formula.append(p)

                    raise Exception(
                        "Incompatibility formula is not correct; no predicate mismatches found."
                    )

                env_pred_state = (incompatibility_formula, incompatible_state)
                return concretized, env_pred_state
            # if not, then we choose the wrong transition
            else:
                if program.deterministic is None:
                    if not is_deterministic(program):
                        raise Exception(
                            "Program is non-deterministic, concretisation of abstract counterexample may not work in this case."
                        )
                elif not program.deterministic:
                    raise Exception(
                        "Program is non-deterministic, concretisation of abstract counterexample may not work in this case."
                    )

                core_unsat = unsat_core(
                    conjunct_formula_set(
                        pred_state
                        + predicate_state_before_incompatibility
                        + [transition_formula(concretized[-1][0])]
                    ),
                    program.symbol_table,
                )
                print("UNSAT CORE: ")
                for c in core_unsat:
                    print("\t" + str(c))
                raise Exception(
                    "Something wrong in abstraction.\nAbstract transition is not satisfiable:\n\n"
                    + str(conjunct_formula_set(predicate_state_before_incompatibility))
                    + "\n"
                    + str(conjunct_formula_set(pred_state))
                    + "\n"
                    + str(transition_formula(concretized[-1][0]))
                    + "\n\n\nAgreed on transitions:\n"
                    + "\n\n".join(map(lambda x: str(x[0]), concretized[:-1]))
                    + "\n\n\nInit state:\n"
                    + str(
                        conjunct_formula_set(
                            preds_in_state(concretized[0][1] | concretized[0][2])
                        )
                    )
                )
        else:
            raise Exception("No incompatibility, what are you doin in here?")


def process_transition_mismatch(program, concretized, incompatible_state):
    if program.deterministic:
        failed_condition = neg(concretized[-1][0].condition)
        reduced = failed_condition.replace(
            {
                Variable(str(v)): Value(concretized[-1][1][str(v)])
                for v in program.env_events + program.con_events
            }
        )
        reduced_simplified = simplify_formula_with_math(reduced, program.symbol_table)

        return (
            concretized[:-1],
            ([reduced_simplified], concretized[-1][1]),
            concretized[-1],
        )
    else:
        raise Exception(
            "Program is non-deterministic, cannot handle refinement for it."
        )
