from __future__ import annotations

import logging

from analysis.abstraction.concretisation import concretize_transitions
from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from analysis.model_checker import ModelChecker
from config import Config
from programs.program import Program
from programs.util import parse_nuxmv_ce_output_finite
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine

from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.strategy_to_nuxmv import strategy_to_nuxmv_model


def compatibility_checking(
    program: Program,
    predicate_abstraction: EffectsAbstraction,
    strategy_machine: MooreMachine | MealyMachine,
    abstract_ltl_problem,
    is_controller: bool,
):
    conf = Config.getConfig()
    if conf.dual and conf.dual2:
        raise ValueError("dual and dual2 are mutually exclusive")
    if conf.dual2:
        if not isinstance(strategy_machine, MealyMachine):
            raise TypeError("dual2 flow expects a MealyMachine strategy")
    else:
        if not isinstance(strategy_machine, MooreMachine):
            raise TypeError("base/dual flow expects a MooreMachine strategy")

    prog = predicate_abstraction.get_program()
    prog_state_props = list(prog.states) + list(prog.bin_state_vars)
    strategy_nuxmv = strategy_to_nuxmv_model(
        strategy_machine,
        prog_state_props,
        prog.out_events,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
        init_choice_logic=abstract_ltl_problem.init_choice_logic,
    )

    mismatch_condition = None

    system = create_nuxmv_model_for_compatibility_checking(
        program,
        strategy_nuxmv,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
        predicate_abstraction.v_to_chain_pred.values(),
        abstract_ltl_problem,
        not program.deterministic,
    )

    logging.info(system)
    contradictory, there_is_mismatch, out = (
        there_is_mismatch_between_program_and_strategy(
            system,
            is_controller,
            mismatch_condition=mismatch_condition,
        )
    )

    if contradictory:
        raise Exception(
            "I have no idea what's gone wrong. Strix thinks the previous mealy machine is a "
            + ("controller" if is_controller else "counterstrategy")
            + ", but nuxmv thinks it is non consistent with the program.\n"
            + "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division."
        )

    if not there_is_mismatch:
        logging.info("No mismatch found.")
        return True, strategy_machine.to_dot(predicate_abstraction.get_all_raw_preds())

    logging.info(out)
    cs_alphabet = [v.name for v in strategy_nuxmv.vars]
    injected_cs_constants = None
    if (
        len(getattr(strategy_machine, "states", [])) == 1
        and "strategy_state" not in cs_alphabet
    ):
        only_state = sorted([str(s) for s in strategy_machine.states], key=str)[0]
        injected_cs_constants = {"strategy_state": only_state}

    agreed_on_transitions_indexed, incompatible_state = parse_nuxmv_ce_output_finite(
        program,
        out,
        cs_alphabet,
        injected_cs_constants=injected_cs_constants,
    )
    agreed_on_execution, disagreed_on_state = concretize_transitions(
        program,
        agreed_on_transitions_indexed,
        incompatible_state,
    )

    return None, (agreed_on_execution, disagreed_on_state)


def there_is_mismatch_between_program_and_strategy(
    system, controller: bool, mismatch_condition=None
):
    model_checker = ModelChecker()
    config = Config.getConfig()
    if config.debug:
        logging.info("Deadlock check")
        # Sanity check
        result, out = model_checker.invar_check(system, "F FALSE", None, True)
        if result:
            logging.info("Are you sure the counterstrategy given is complete?")
            return True, None, out

    # hack: if env_lose is used in system, i.e. it appears as a word
    env_lose_logic = " | env_lose" if "\tenv_lose :" in system else ""

    if not controller or config.getConfig().dual2:
        if not mismatch_condition:
            there_is_no_mismatch, out = model_checker.invar_check(
                system, "compatible" + env_lose_logic, None, config.mc
            )
        else:
            mismatch_condition_s = (
                mismatch_condition
                if isinstance(mismatch_condition, str)
                else str(mismatch_condition)
            )
            there_is_no_mismatch, out = model_checker.invar_check(
                system,
                "!(!compatible" + " & " + mismatch_condition_s + ")" + env_lose_logic,
                None,
                config.mc,
            )
            if there_is_no_mismatch:
                there_is_no_mismatch, out = model_checker.invar_check(
                    system, "compatible" + env_lose_logic, None, config.mc
                )
        return False, not there_is_no_mismatch, out

    else:
        return False, False, None
