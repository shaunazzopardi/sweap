from __future__ import annotations

import logging

import config
from analysis.abstraction.effects_abstraction.effects_abstraction import (
    EffectsAbstraction,
)
from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import implies, conjunct, X, normalize_ltl
from synthesis.machines.machine import Machine
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine

from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.strategy_to_nuxmv import strategy_to_nuxmv_model
from analysis.model_checker import ModelChecker


def _append_invariants(system: str, invariants: list[str]) -> str:
    extra = [inv for inv in invariants if inv]
    if not extra:
        return system
    suffix = "".join(f"\nINVAR\n\t({inv})" for inv in extra)
    return system + suffix + "\n"


def create_nuxmv_model_for_verification_checking(
    program: Program,
    strategy_model,
    predicate_abstraction: EffectsAbstraction,
    abstract_ltl_problem,
    init_choice_logic_expr: str | None = None,
) -> str:
    system = create_nuxmv_model_for_compatibility_checking(
        program,
        strategy_model,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
        predicate_abstraction.v_to_chain_pred.values(),
        init_choice_logic_expr=init_choice_logic_expr,
    )

    env_lose = any(v.name == "env_lose" for v in strategy_model.vars)
    return _append_invariants(system, ["compatible", "!env_lose" if env_lose else ""])


def _init_choice_logic_for_main_init(
    machine: Machine, abstract_ltl_problem
) -> str | None:
    init_choice_logic = getattr(abstract_ltl_problem, "init_choice_logic", None)
    if init_choice_logic is None:
        return None

    # for the dual and dual2 cases we are performing the init transition in one step
    init_choice_logic = init_choice_logic.replace_formulas(
        lambda f: (
            f.right
            if isinstance(f, UniOp) and (f.op == "next" or f.op == "X")
            else None
        )
    )

    conf = config.Config.getConfig()
    if conf.dual2 and isinstance(machine, MooreMachine):
        return init_choice_logic.to_nuxmv()

    if conf.dual and isinstance(machine, MealyMachine):
        return init_choice_logic.to_nuxmv()

    return None


def verify_strategy(
    program: Program,
    predicate_abstraction: EffectsAbstraction,
    machine: Machine,
    original_ltl_spec,
    abstract_ltl_problem,
):
    conf = config.Config.getConfig()

    strategy_nuxmv = strategy_to_nuxmv_model(
        machine,
        predicate_abstraction.get_program().bin_state_vars,
        predicate_abstraction.get_program().out_events,
        predicate_abstraction.get_state_predicates(),
        predicate_abstraction.get_transition_predicates(),
        for_verification=True,
        init_choice_logic=abstract_ltl_problem.init_choice_logic,
    )
    init_choice_logic_expr = _init_choice_logic_for_main_init(
        machine, abstract_ltl_problem
    )

    system = create_nuxmv_model_for_verification_checking(
        program,
        strategy_nuxmv,
        predicate_abstraction,
        abstract_ltl_problem,
        init_choice_logic_expr=init_choice_logic_expr,
    )
    logging.info(system)

    bin_conditions = []
    for chain_pred in predicate_abstraction.v_to_chain_pred.values():
        if not conf.dual and not conf.dual2 and chain_pred.is_input:
            continue
        ch_pred_bin_conds = []
        bin_vars = set(chain_pred.bin_vars)
        for rep in chain_pred.bin_rep.values():
            missing_bin_vars = bin_vars.difference(rep.variablesin())
            for m in missing_bin_vars:
                ch_pred_bin_conds.append(
                    implies(conjunct(rep, X(rep)), BiOp(m, "<->", X(m)))
                )
        bin_conditions.extend(ch_pred_bin_conds)

    bound = 50
    contradictory, there_is_mismatch, out = (
        there_is_mismatch_between_program_and_controller(
            system,
            original_ltl_spec,
            predicate_abstraction.structural_loop_constraints + bin_conditions,
            any(v.name == "env_lose" for v in strategy_nuxmv.vars),
            bound,
        )
    )

    role_name = str(getattr(machine, "name", "")).lower()
    if "counterstrategy" in role_name:
        role = "counterstrategy"
    elif "controller" in role_name:
        role = "controller"
    else:
        role = "counterstrategy" if conf.dual2 else "controller"

    if contradictory:
        raise Exception(
            "I have no idea what's gone wrong. Strix thinks the previous strategy machine is a "
            + role
            + ", but nuxmv thinks it is non consistent with the program."
        )

    if there_is_mismatch:
        if "Maximum bound reached" in out:
            print(
                role
                + " correct up to "
                + str(bound)
                + " IC3 steps, I do not verify beyond this."
            )
            return True
        logging.info(out)
        logging.info(str(machine))
        print(str(machine))
        raise Exception(
            role
            + " does not enforce the required LTL property on the program:\n"
            + str(out)
        )

    print(out)
    print(role + " enforces the required LTL property!")
    return True


def there_is_mismatch_between_program_and_controller(
    system, ltlspec, loop_constraints, env_lose, bound
):
    model_checker = ModelChecker()
    dual = config.Config.getConfig().dual
    dual2 = config.Config.getConfig().dual2
    logging.info(system)
    # Sanity check
    result, out = model_checker.invar_check(system, "F FALSE", None, True)
    if result:
        logging.info("Are you sure the controller given is complete?")
        return True, False, None

    if len(loop_constraints) > 0:
        loop_constraints_str = (
            "(G(("
            + ") & (".join(map(lambda x: x.to_nuxmv(), loop_constraints))
            + "))) -> "
        )
    else:
        loop_constraints_str = ""

    spec = str(normalize_ltl(ltlspec))
    if dual2:
        spec = "!" + spec
    objective = loop_constraints_str + " (" + spec + ")"
    if dual:
        objective = "X(" + objective + ")"

    print(objective)

    there_is_no_mismatch, out = model_checker.invar_check(
        system,
        objective,
        bound,
        True,
    )

    return False, not there_is_no_mismatch, out
