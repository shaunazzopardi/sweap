import logging
import os
import subprocess
import config

from tempfile import NamedTemporaryFile
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem
from synthesis.machines.wrapped_hoa import WrappedHOA

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../../../binaries/strix_tlsf_file.sh"))
semml_path = str(os.path.join(dirname, "../../../binaries/semml/semml.py"))


def ltl_synthesis(synthesis_problem: LTLSynthesisProblem, symbol_table) -> WrappedHOA:
    try:
        logging.info(synthesis_problem.tlsf)
        with NamedTemporaryFile("w", suffix=".tlsf", delete=False) as tmp:
            tmp.write(synthesis_problem.tlsf)
            tmp.close()

            backend = config.Config.getConfig().backend
            if backend == "strix":
                cmd = f"{strix_path} {tmp.name} -m both --onthefly none"
            elif backend == "semml":
                cmd = f"{semml_path} --tlsf {tmp.name}"
            else:
                raise Exception("Unrecognised synthesis backend " + str(backend))

            try:
                so = subprocess.getstatusoutput(cmd)
                output: str = so[1]
                logging.info(output)

                out_lines = output.split("\n")
                real = out_lines[0]
                hoa = "\n".join(out_lines[1:])
            except Exception as err:
                logging.info(err)
                if "Killed" in str(err):
                    raise Exception(
                        "OutOfMemory: Finite synthesis engine was killed. Try increasing the memory limit."
                    )
                else:
                    raise err

            if "UNREALIZABLE" in real:
                logging.info(
                    "\nINFO: Finite synthesis engine thinks the current abstract problem is unrealisable! I will check..\n"
                )
                return WrappedHOA(hoa, False, synthesis_problem, symbol_table)
            elif "REALIZABLE" in real:
                logging.info(
                    "\nINFO: Finite synthesis engine determines the current abstract problem realisable!\n"
                )
                return WrappedHOA(hoa, True, synthesis_problem, symbol_table)
            else:
                raise Exception(
                    "Finite synthesis engine not returning appropriate value.\n\n"
                    + cmd
                    + "\n\n"
                    + output
                    + "\n\n"
                    + synthesis_problem.tlsf
                )
    except Exception as err:
        raise err
