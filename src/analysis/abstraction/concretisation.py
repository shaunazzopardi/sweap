from pysmt.shortcuts import And

from analysis.smt_checker import check
from programs.util import (
    stutter_transition,
    preds_in_state,
    transition_formula,
    add_prev_suffix,
)
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
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
    true,
    atomic_predicates,
    is_tautology,
    is_contradictory,
)
from prop_lang.value import Value
from prop_lang.variable import Variable


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

    # two options, either we stopped because of a predicate mismatch, or a transition mismatch
    incompatibility_formula = []
    if (
        incompatible_state[2]["compatible_states"] == "FALSE"
        or incompatible_state[2]["compatible_outputs"] == "FALSE"
    ):
        # TODO
        if not program.deterministic:
            raise Exception(
                "Program is non-deterministic, we do not handle refinement for it."
            )
        failed_condition = neg(concretized[-1][0].condition)
        reduced = failed_condition.replace(
            [
                BiOp(Variable(str(v)), ":=", Value(concretized[-1][2][str(v)]))
                for v in program.env_events + program.con_events
            ]
        )
        reduced_simplified = simplify_formula_with_math(reduced, program.symbol_table)
        reduced_normalised = reduced_simplified.replace_formulas(
            lambda x: normalise_mathexpr(x) if isinstance(x, MathExpr) else None
        )

        return concretized[:-1], ([reduced_normalised], concretized[-1])

        # return process_transition_mismatch(program,
        #                                    concretized,
        #                                    incompatible_state)
    else:
        if (
            incompatible_state[2]["compatible_state_predicates"] == "FALSE"
            or incompatible_state[2]["compatible_tran_predicates"] == "FALSE"
        ):
            pred_state = preds_in_state(incompatible_state[2])
            predicate_state_before_incompatibility = [
                add_prev_suffix(p)
                for p in preds_in_state(concretized[-1][2])
                if "_prev" not in str(p)
            ]
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
                    var_state = [
                        BiOp(v, "=", Value(incompatible_state[1][str(v)]))
                        for v in p.variablesin()
                    ]
                    if not sat(
                        conjunct_formula_set([p] + var_state),
                        program.symbol_table,
                    ):
                        incompatibility_formula.append(p)

                if (
                    incompatibility_formula == neg(true())
                    or incompatibility_formula == true()
                ):
                    raise Exception("Incompatibility formula is not correct")

                env_pred_state = (incompatibility_formula, incompatible_state)
                return concretized, env_pred_state
            # if not, then we choose the wrong transition
            else:
                raise Exception(
                    "Something wrong in abstraction.\nAbstract transition is not satisfiable:\n\n"
                    + str(
                        conjunct_formula_set(
                            [
                                add_prev_suffix(p)
                                for p in preds_in_state(concretized[-1][2])
                            ]
                        )
                    )
                    + "\n"
                    + str(conjunct_formula_set(pred_state))
                    + "\n"
                    + str(transition_formula(concretized[-1][0]))
                )

                # failed_condition = concretized[-1][0].condition
                # reduced = failed_condition.replace([BiOp(Variable(str(v)), ":=", Value(concretized[-1][2][str(v)]))
                #                                     for v in program.env_events + program.con_events])
                # if is_tautology(reduced, program.symbol_table):
                #     raise Exception("Something wrong in abstraction: " +
                #                     "effect of mismatched transition is not modelled precisely enough: " + "\n" +
                #                     "transition: " + str(concretized[-1][0]) + "\n" +
                #                     "now: " + ", ".join(map(str, preds_in_state(concretized[-1][2]))) + "\n" +
                #                     "next: " + ", ".join(map(str, preds_in_state(incompatible_state[2]))))
                # elif is_contradictory(reduced, program.symbol_table):
                #     raise Exception("Something wrong in LTL or compatibility checking, transition guard is false but taken: " +
                #                     "transition: " + str(concretized[-1][0]))
                # reduced_simplified = neg(simplify_formula_with_math(reduced, program.symbol_table))
                # reduced_normalised = reduced_simplified.replace_formulas(
                #     lambda x: normalise_mathexpr(x) if isinstance(x, MathExpr) else None)
                #
                # if reduced_normalised == neg(true()) or reduced_normalised == true():
                #     raise Exception("Incompatibility formula is not correct")
                #
                # return concretized[:-1], ([reduced_normalised], concretized[-1])

                # return process_transition_mismatch(program,
                #                                     concretized,
                #                                     incompatible_state)


def process_transition_mismatch(program, concretized, incompatible_state):
    if program.deterministic:
        failed_condition = neg(concretized[-1][0].condition)
        reduced = failed_condition.replace(
            [
                BiOp(Variable(str(v)), ":=", Value(concretized[-1][1][str(v)]))
                for v in program.env_events + program.con_events
            ]
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
        # if program is not deterministic, we need to identify the transitions the counterstrategy wanted to take rather than the one the program actually took
        try:
            state_before_mismatch = concretized[-2][1]
        except Exception as e:
            raise e
        src_state = concretized[-2][0].tgt
        tgt_state_env_wanted = [
            p for p in program.states if incompatible_state["mon_" + str(p)] == "TRUE"
        ][0]
        outputs_env_wanted = [
            p
            for p in program.out_events
            if incompatible_state["mon_" + str(p)] == "TRUE"
        ]
        outputs_env_wanted += [
            neg(p)
            for p in program.out_events
            if incompatible_state["mon_" + str(p)] == "FALSE"
        ]
        if incompatible_state["turn"] == "mon_env":
            candidate_transitions = [
                t
                for t in program.transitions
                if t.src == src_state
                and t.tgt == tgt_state_env_wanted
                and set(t.output) == set(outputs_env_wanted)
            ]
            if tgt_state_env_wanted == src_state:
                stutter = stutter_transition(program, src_state, True)
                if stutter is not None:
                    candidate_transitions.append(stutter)
        elif incompatible_state["turn"] == "mon_con":
            candidate_transitions = [
                t
                for t in program.con_transitions
                if t.src == src_state
                and t.tgt == tgt_state_env_wanted
                and set(t.output) == set(outputs_env_wanted)
            ]
            if tgt_state_env_wanted == src_state:
                stutter = stutter_transition(program, src_state, False)
                if stutter is not None:
                    candidate_transitions.append(stutter)
        else:
            raise Exception("Mismatches should only occur at mon_env or mon_con turns")

        compatible_with_abstract_state = []
        for str_p in state_before_mismatch.keys():
            if is_predicate_var(str_p):
                p = Variable(str_p)
                if state_before_mismatch[str_p] == "TRUE":
                    compatible_with_abstract_state += [var_to_predicate(p)]
                else:
                    compatible_with_abstract_state += [neg(var_to_predicate(p))]

        abstract_state = conjunct_formula_set(compatible_with_abstract_state)
        env_desired_transitions = [
            t
            for t in candidate_transitions
            if check(
                And(
                    *abstract_state.to_smt(program.symbol_table),
                    *t.condition.to_smt(program.symbol_table)
                )
            )
        ]
        formula = disjunct_formula_set(
            [t.condition for t in env_desired_transitions]
            + [propagate_negations(neg(concretized[-1][0].condition))]
        )
        return (
            concretized[:-1],
            ([formula], concretized[-1][1]),
            concretized[-1],
        )
