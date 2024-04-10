import logging
import subprocess
from tempfile import NamedTemporaryFile
from typing import Tuple

from parsing.hoa_parser import hoa_to_transitions
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction
from synthesis.abstract_ltl_synthesis_problem import AbstractLTLSynthesisProblem
from synthesis.mealy_machine import MealyMachine
from prop_lang.variable import Variable
from synthesis.moore_machine import MooreMachine


def ltl_synthesis(synthesis_problem: AbstractLTLSynthesisProblem) -> Tuple[bool, str]:
    tlsf_script = synthesis_problem.to_tlsf()
    logging.info(tlsf_script)
    try:
        with (NamedTemporaryFile('w', suffix='.tlsf', delete=False) as tmp):
            tmp.write(tlsf_script)
            tmp.close()

            # cmd = strix_tlsf_command + " -v '" + tmp.name + "':./spec.tlsf -m both "
            # cmd = "docker run" + " -v " + tmp.name + ":/spec.tlsf" + \
            # " --entrypoint ./strix/scripts/strix_tlsf_file.sh strix_tlsf_file /spec.tlsf" + " -m both --onthefly none"
            # " --entrypoint ./strix/scripts/strix_tlsf_file.sh strix_tlsf_file /spec.tlsf" + ""
            cmd = f"strix_tlsf.sh {tmp.name} -m both --onthefly none"

            so = subprocess.getstatusoutput(cmd)
            output: str = so[1]
            logging.info(output)

            if "UNREALIZABLE" in output:
                logging.info("\nINFO: Strix thinks the current abstract problem is unrealisable! I will check..\n")
                # mon = parse_hoa(env_events=synthesis_problem.env_props, con_events=synthesis_problem.con_props, output=output)
                return False, output#mon
            elif "REALIZABLE" in output:
                logging.info("\nINFO: Strix thinks the current abstract problem is realisable! I will check..\n")
                try:
                    # mon = parse_hoa(env_events=synthesis_problem.env_props, con_events=synthesis_problem.con_props, output=output)
                    return True, output#mon
                except Exception as err:
                    raise err
            else:
                raise Exception(
                    "Strix not returning appropriate value.\n\n" + cmd + "\n\n" + output + "\n\n" + tlsf_script)
    except Exception as err:
        raise err
    pass


def parse_hoa(synthesis_problem: AbstractLTLSynthesisProblem,
              output: object,
              env_con_separate: bool,
              abstraction: PredicateAbstraction,
              one_trans: bool) -> MealyMachine:
    if "UNREALIZABLE" in output:
        counterstrategy = True
    else:
        counterstrategy = False

    logging.info(output)

    # logger.info("Parsing Strix output..")
    init_st, trans = hoa_to_transitions(output)
    # logger.info("Finished parsing Strix output.. Constructing expanded Mealy Machine now..")

    env_props = (synthesis_problem.get_env_props()
                 + synthesis_problem.get_program_out_props()
                 + synthesis_problem.get_program_pred_props())

    con_props = synthesis_problem.get_con_props()

    if one_trans and counterstrategy:
        mon = MooreMachine("counterstrategy", init_st,
                           env_props,
                           con_props,
                           {})
        mon.add_transitions(trans, abstraction.get_symbol_table())
        return mon

    if not env_con_separate:
        mon = MealyMachine("counterstrategy" if counterstrategy else "controller", init_st,
                           env_props,
                           con_props,
                           {}, {})
        mon.add_transitions(trans)
    else:
        mon = MealyMachine("counterstrategy" if counterstrategy else "controller", init_st,
                           env_props,
                           con_props,
                           {},
                           {})

        mon.add_transitions_env_con_separate(not counterstrategy,
                                             trans,
                                             synthesis_problem,
                                             abstraction)

    return mon


# this does what ./scripts/strix_tlsf.sh does
def syfco_ltl(tlsf_file: str) -> str:
    try:
        LTL_cmd = 'syfco -f ltl -q double -m fully ' + tlsf_file
        so = subprocess.getstatusoutput(LTL_cmd)
        LTL_str: str = so[1]
        # LTL = string_to_ltl(LTL_str.replace("\"", ""))

        return LTL_str
    except Exception as err:
        raise err
    pass


def syfco_ltl_in(tlsf_file: str):
    try:
        INS_cmd = 'syfco -f ltl --print-input-signals ' + tlsf_file
        so = subprocess.getstatusoutput(INS_cmd)
        INS_str: str = so[1]
        INS = [Variable(a.strip(" ")) for a in INS_str.split(",")]

        return INS
    except Exception as err:
        raise err
    pass


def syfco_ltl_out(tlsf_file: str):
    try:
        OUTS_cmd = 'syfco -f ltl --print-output-signals ' + tlsf_file
        so = subprocess.getstatusoutput(OUTS_cmd)
        OUTS_str: str = so[1]
        OUTS = [Variable(a.strip(" ")) for a in OUTS_str.split(",")]

        return OUTS
    except Exception as err:
        raise err
    pass
