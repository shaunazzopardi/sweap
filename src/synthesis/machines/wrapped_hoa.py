import logging
import time

import config
from parsing.hoa_parser import hoa_to_transitions
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.machines.machine import Machine
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class WrappedHOA:
    hoa: str
    is_controller: bool
    machine: Machine

    def __init__(
        self,
        _hoa: str,
        _is_controller: bool,
        symbol_table,
        synthesis_problem: AbstractLTLSynthesisProblem,
    ):
        self.hoa = _hoa
        self.is_controller = _is_controller

        print("massaging hoa")
        self.__to_machine(symbol_table, synthesis_problem)

    def __to_machine(
        self,
        synthesis_problem: AbstractLTLSynthesisProblem,
        symbol_table,
    ):
        start = time.time()

        init_st, trans = hoa_to_transitions(self.hoa)

        env_props = (
            synthesis_problem.get_env_props()
            + synthesis_problem.get_program_out_props()
            + synthesis_problem.get_program_pred_props()
        )

        con_props = synthesis_problem.get_con_props()

        if not self.is_controller:
            mm = MooreMachine("counterstrategy", init_st, env_props, con_props, {})
            mm.add_transitions(trans, symbol_table)
        else:
            mm = MealyMachine(
                "controller",
                init_st,
                env_props,
                con_props,
                {},
                {},
            )
            mm.add_transitions(trans)

            if config.Config.getConfig().dual:
                # mm = mm.to_moore_machine()
                self.is_controller = False
                logging.info("Unrealizable")
            else:
                logging.info("Realizable")

        logging.info(mm)
        logging.info("massaging hoa took " + str(time.time() - start))

        self.machine = mm
