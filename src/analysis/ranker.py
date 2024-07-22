import logging
import os
import subprocess
import time
from tempfile import NamedTemporaryFile
from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from shutil import which
from pathlib import Path

class Ranker:

    def check(self, main_function: str, only_check_for_termination=True):
        with NamedTemporaryFile('w', suffix='.c', delete=False) as tmp:
            tmp.write(main_function)
            tmp.close()

            try:
                start = time.time()
                cpa_path = Path("./binaries/CPAchecker-2.3-unix/scripts/").resolve()
                # cpa_path = Path(which("cpa.sh")).resolve().parent
                bench = ('-benchmark -heap 1024M ' if only_check_for_termination else '')
                cmd = (
                    f"./binaries/CPAchecker-2.3-unix/scripts/cpa.sh  -preprocess -terminationAnalysis {bench} "
                    f'{tmp.name} -spec {cpa_path}/../config/properties/termination.prp'
                )
                
                out = subprocess.getstatusoutput(cmd)
                logging.info("cpachecker took " + str(time.time() - start))
                out = str(out)
                if "Verification result: UNKNOWN" in out:
                    return False, None
                elif "Verification result: FALSE" in out:
                    return False, None
                elif "Verification result: TRUE" in out:
                    out = out.replace("\\n", "\n")
                    try:
                        term_arg = out.split("Termination argument consisting of:")[1].strip().split("\n")

                        ranking_function = term_arg[0].replace("Ranking function ", "").replace("main::", "")
                        ranking_function = ranking_function \
                            .removeprefix(ranking_function.split(") = ")[0]) \
                            .removeprefix(") = ")

                        invars = term_arg[1].replace("main::", "") \
                            .replace("Supporting invariants ", "") \
                            .replace("[", "") \
                            .replace("]", "") \
                            .split(",")
                        if '' in invars:
                            invars.remove('')

                        if "-nested ranking function" in ranking_function:
                            logging.info("Termination proved, but could only find a nested ranking function, "
                                         "I do not deal with this yet unfortunately for you..: " + str(
                                ranking_function))
                            return True, None

                        logging.info(main_function + "\n" + out)
                        return True, (string_to_math_expression(ranking_function).simplify(),
                                      [string_to_prop(invar) for invar in invars])

                    except:
                        logging.info(
                            "WARNING: Function terminates, but there is no ranking function, are you sure the loop has at least one iteration?")
                        return True, None
                else:
                    logging.info(out)
                    raise Exception(out +
                                    "\n\nUnexpected result during termination checking of:\n" + main_function)
            except subprocess.CalledProcessError as err:
                raise Exception(err.output + "\n\n" + out)
            except Exception as err:
                logging.info(str(err))
                raise err
            finally:
                os.remove(tmp.name)
