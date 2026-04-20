import config
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
    sat,
    simplify_formula_with_math,
    var_to_predicate,
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
    # compatibility phase, so they must be filtered out.
    if _is_initial_compat_phase(cs_state):
        return [p for p in preds if not _is_transition_like_predicate_formula(p)]
    return preds


def _mismatched_preds_from_comp_macros(cs_state):
    mismatches = []
    for key, value in cs_state.items():
        if value != "FALSE" or not key.startswith("comp_pred_"):
            continue
        pred_name = key.removeprefix("comp_")
        if pred_name not in cs_state:
            continue
        base = var_to_predicate(Variable(pred_name))
        pred_value = cs_state[pred_name]
        if pred_value == "TRUE":
            mismatch = base
        elif pred_value == "FALSE":
            mismatch = neg(base)
        else:
            continue
        if mismatch not in mismatches:
            mismatches.append(mismatch)
    return mismatches


def _reduce_to_mismatched_predicates(
    pred_state, incompatible_state, symbol_table
) -> set:
    reduced = set()
    for p in pred_state:
        var_state = [
            BiOp(
                v,
                "=",
                Value((incompatible_state[1] | incompatible_state[2])[str(v)]),
            )
            for v in p.variablesin()
        ]
        if not sat(conjunct_formula_set([p] + var_state), symbol_table):
            reduced.add(p)
    return reduced


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
            if stutter_trans is None:
                raise Exception("stuttering transition not found")
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
            macro_mismatches = _mismatched_preds_from_comp_macros(incompatible_state[2])
            if len(macro_mismatches) > 0:
                return concretized, (macro_mismatches, incompatible_state)

            # incompatibility_formula = _reduce_to_mismatched_predicates(
            #     pred_state,
            #     incompatible_state,
            #     program.symbol_table,
            # )
            # if len(incompatibility_formula) > 0:
            #     return concretized, (incompatibility_formula, incompatible_state)

            if config.Config.getConfig().debug and len(concretized) > 0:
                incompatibility_formula = _reduce_to_mismatched_predicates(
                    pred_state,
                    incompatible_state,
                    program.symbol_table,
                )
                if incompatibility_formula != set(macro_mismatches):
                    diff = incompatibility_formula.difference(macro_mismatches)
                    err = (
                        "nuXmv determined the following mismatches: "
                        + ", ".join(map(str, macro_mismatches))
                        + "\n"
                        + "However, the actual mismatches are: "
                        + ", ".join(map(str, macro_mismatches))
                        + "\n"
                        + "They disagree on: "
                        + ", ".join(map(str, diff))
                    )
                    raise Exception(err)

                predicate_state_before_incompatibility = _filter_preds_for_compat_state(
                    [
                        add_prev_suffix(p)
                        for p in preds_in_state(concretized[-1][2])
                        if not any(v for v in p.variablesin() if "_prev" in str(v))
                    ],
                    concretized[-1][2],
                )

                if not sat(
                    conjunct_formula_set(
                        pred_state
                        + predicate_state_before_incompatibility
                        + [transition_formula(concretized[-1][0])]
                    ),
                    program.symbol_table,
                ):

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
                        + str(
                            conjunct_formula_set(predicate_state_before_incompatibility)
                        )
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
                    raise Exception(
                        "Somethings going wrong.. Run with --log and inspect nuXmv model."
                    )

            raise Exception(
                "Incompatibility formula is not correct; no predicate mismatches found."
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
