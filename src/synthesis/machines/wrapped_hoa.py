import logging
import time

import config
from parsing.hoa_parser import hoa_to_transitions
from prop_lang.types.types import BOOLEAN
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.machines.machine import Machine
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class WrappedHOA:
    hoa: str
    realisable: bool
    machine: Machine

    def __init__(
        self,
        _hoa: str,
        realisable: bool,
        symbol_table,
        synthesis_problem: AbstractLTLSynthesisProblem,
    ):
        self.hoa = _hoa
        self.realisable = realisable

        print("massaging hoa")
        self.__to_machine(symbol_table, synthesis_problem)

    def __to_machine(
        self,
        synthesis_problem: AbstractLTLSynthesisProblem,
        symbol_table,
    ):
        start = time.time()

        init_st, trans = hoa_to_transitions(self.hoa, self.realisable)

        env_props = (
            synthesis_problem.get_env_props()
            + synthesis_problem.get_program_out_props()
            + synthesis_problem.get_program_pred_props()
        )

        con_props = synthesis_problem.get_con_props()

        for k in trans.keys():
            (src, env, tgt) = k
            con = trans[k]
            if any(v for v in env.variablesin() if v not in env_props):
                raise Exception(
                    "Transition condition uses environment variable not in synthesis problem: "
                    + str(env)
                )
            if any(v for c in con for v in c.variablesin() if v not in con_props):
                raise Exception(
                    "Transition condition uses controller variable not in synthesis problem: "
                    + str(con)
                )

        dual = config.Config.getConfig().dual
        dual2 = config.Config.getConfig().dual2
        if dual:
            if self.realisable:
                name = "counterstrategy"
                logging.info("Unrealizable")
            else:
                name = "controller"
                logging.info("Realizable")
        else:
            if self.realisable:
                name = "controller"
                logging.info("Realizable")
            else:
                name = "counterstrategy"
                logging.info("Unrealizable")

        if dual or dual2:
            # to add env_int props
            symbol_table.update({v.name: BOOLEAN for v in env_props})

        if not self.realisable:
            mm = MooreMachine(name, init_st, env_props, con_props)
            mm.add_transitions(trans, symbol_table)
        else:
            mm = MealyMachine(
                name,
                init_st,
                env_props,
                con_props,
            )
            mm.add_transitions(trans)

            if config.Config.getConfig().dual:
                logging.info("Unrealizable")
            else:
                logging.info("Realizable")

        logging.info(mm)
        logging.info("massaging hoa took " + str(time.time() - start))

        self.machine = mm
