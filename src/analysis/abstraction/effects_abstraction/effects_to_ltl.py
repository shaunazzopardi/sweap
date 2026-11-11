import analysis.abstraction.effects_abstraction.to_ltl.to_env_con_separate_ltl as to_env_con_separate_ltl
import analysis.abstraction.explicit_abstraction.to_ltl as explicit_to_ltl
from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.abstraction.effects_abstraction.to_ltl import one_trans_to_ltl
from analysis.abstraction.interface.ltl_abstraction_type import (
    LTLAbstractionType,
    LTLAbstractionBaseType,
    LTLAbstractionStructureType,
    LTLAbstractionTransitionType,
    LTLAbstractionOutputType,
)
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem


def to_ltl(
    effects_abstraction: EffectsAbstraction,
    original_ltl_problem: LTLSynthesisProblem,
    ltlAbstractionType: LTLAbstractionType,
) -> AbstractLTLSynthesisProblem:
    if (
        ltlAbstractionType.base_type == LTLAbstractionBaseType.effects_representation
        and ltlAbstractionType.transition_type == LTLAbstractionTransitionType.one_trans
        and ltlAbstractionType.structure_type
        == LTLAbstractionStructureType.control_state
        and ltlAbstractionType.output_type == LTLAbstractionOutputType.no_output
    ):
        return one_trans_to_ltl.abstract_ltl_problem(
            original_ltl_problem, effects_abstraction
        )

    if (
        ltlAbstractionType.base_type == LTLAbstractionBaseType.explicit_automaton
        and ltlAbstractionType.transition_type == LTLAbstractionTransitionType.combined
        and ltlAbstractionType.structure_type
        == LTLAbstractionStructureType.control_and_predicate_state
        and ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env
    ):
        raise NotImplementedError(
            "Explicit automaton LTL abstraction not implemented for effects abstraction"
        )
        # effects_abstraction.combined_automata_abstraction = (
        #     effects_abstraction.to_automaton_abstraction()
        # )
        # return (
        #     effects_abstraction.combined_automata_abstraction,
        #     explicit_to_ltl.abstract_ltl_problem(
        #         original_ltl_problem,
        #         effects_abstraction,
        #         effects_abstraction.combined_automata_abstraction,
        #     ),
        # )
    elif (
        ltlAbstractionType.base_type == LTLAbstractionBaseType.effects_representation
        and ltlAbstractionType.structure_type
        == LTLAbstractionStructureType.control_state
        and ltlAbstractionType.output_type == LTLAbstractionOutputType.after_env
    ):
        if (
            ltlAbstractionType.transition_type
            == LTLAbstractionTransitionType.env_con_separate
        ):
            raise NotImplementedError(
                "Options for LTL abstraction not implemented: "
                + str(ltlAbstractionType)
            )
            # return (
            #     effects_abstraction,
            #     to_env_con_separate_ltl.abstract_ltl_problem(
            #         original_ltl_problem, effects_abstraction
            #     ),
            # )
        elif (
            ltlAbstractionType.transition_type
            == LTLAbstractionTransitionType.env_con_separate_organised_by_effects
        ):
            raise NotImplementedError(
                "Options for LTL abstraction not implemented: "
                + str(ltlAbstractionType)
            )
            # return (
            #     effects_abstraction,
            #     to_env_con_separate_ltl.abstract_ltl_problem(
            #         original_ltl_problem, effects_abstraction, True
            #     ),
            # )

    raise NotImplementedError(
        "Options for LTL abstraction not implemented: " + str(ltlAbstractionType)
    )
