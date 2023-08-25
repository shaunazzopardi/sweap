import subprocess
from tempfile import NamedTemporaryFile
from typing import Tuple

from parsing.hoa_parser import hoa_to_transitions
from programs.program import Program
from programs.synthesis.mealy_machine import MealyMachine
from programs.synthesis.ltl_synthesis_problem import LTLSynthesisProblem
from prop_lang.variable import Variable


def ltl_synthesis(synthesis_problem: LTLSynthesisProblem) -> Tuple[bool, MealyMachine]:
    tlsf_script = synthesis_problem.to_tlsf()
    print(tlsf_script)
    try:
        with NamedTemporaryFile('w', suffix='.tlsf', delete=False) as tmp:
            tmp.write(tlsf_script)
            tmp.close()

            # cmd = strix_tlsf_command + " -v '" + tmp.name + "':./spec.tlsf -m both "
            cmd = "docker run" + " -v " + tmp.name + ":/spec.tlsf" + " --entrypoint ./strix/scripts/strix_tlsf_file.sh strix_tlsf_file /spec.tlsf" + " -m both"

            so = subprocess.getstatusoutput(cmd)
            output: str = so[1]

            if "UNREALIZABLE" in output:
                print("\nINFO: Strix thinks the current abstract problem is unrealisable! I will check..\n")
                mon = parse_hoa(env_events=synthesis_problem.env_props, con_events=synthesis_problem.con_props, output=output)
                return False, mon
            elif "REALIZABLE" in output:
                print("\nINFO: Strix thinks the current abstract problem is realisable! I will check..\n")
                try:
                    mon = parse_hoa(env_events=synthesis_problem.env_props, con_events=synthesis_problem.con_props, output=output)
                    return True, mon
                except Exception as err:
                    raise err
            else:
                raise Exception(
                    "Strix not returning appropriate value.\n\n" + cmd + "\n\n" + output + "\n\n" + tlsf_script)
    except Exception as err:
        raise err
    pass


def parse_hoa(env_events, con_events, output) -> Program:
    if "UNREALIZABLE" in output:
        counterstrategy = True
    else:
        counterstrategy = False

    print(output)

    init_st, trans = hoa_to_transitions(output)

    mon = MealyMachine("counterstrategy" if counterstrategy else "controller", "st_" + init_st, env_events, con_events, {}, {})

    mon.add_transitions(trans)
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
