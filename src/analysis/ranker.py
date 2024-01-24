import logging
import os
import subprocess
import time
from tempfile import NamedTemporaryFile
from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression

class Ranker:

    def check(self, main_function: str, only_check_for_termination=True):
        with NamedTemporaryFile('w', suffix='.c', delete=False) as tmp:
            tmp.write(main_function)
            tmp.close()

            try:
                start = time.time()

                cmd = ['(/cpachecker/scripts/cpa.sh -preprocess -terminationAnalysis /workdir/prog.c -spec '
                    '/cpachecker/config/properties/termination.prp) && cat output/terminationAnalysisResult.txt']

                img = "registry.gitlab.com/sosy-lab/software/cpachecker:latest"
                out = client.containers.run(img, command=cmd, entrypoint=["/bin/bash", "-c"],
                                            volumes={tmp.name: {'bind': '/workdir/prog.c', 'mode': 'rw'}},
                                            remove=True, stdout=True, stderr=True).decode('utf-8')
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
                        return True, (string_to_math_expression(ranking_function).simplify(), [string_to_prop(invar) for                                                                                      invar in
                                                                                        invars])
                    except Exception as err:
                        logging.info(
                            "WARNING: Function terminates, but there is no ranking function, are you sure the loop has at least one iteration?")
                        return True, None
                else:
                    logging.info(out)
                    raise Exception("Make sure cpachecker is available. "
                                    "Unexpected result during termination checking of:\n" + main_function)
            except subprocess.CalledProcessError as err:
                raise Exception(err.output + "\n\n" + out)
            except Exception as err:
                logging.info(str(err))
                raise err
            finally:
                os.remove(tmp.name)
