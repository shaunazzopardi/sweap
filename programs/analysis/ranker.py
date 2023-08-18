import os
import subprocess
from tempfile import NamedTemporaryFile

from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression


class Ranker:
    def check(self, main_function: str):
        with NamedTemporaryFile('w', suffix='.c', delete=False) as tmp:
            tmp.write(main_function)
            tmp.close()

            try:
                cmd = "docker run -v " + tmp.name + ":/workdir/prog.c" + " -v ./output:/output" + " --entrypoint /bin/bash cpachecker -c " + \
                      '"(rm -r -f ./output); (/cpachecker/scripts/cpa.sh  -preprocess -terminationAnalysis /workdir/prog.c -spec /cpachecker/config/properties/termination.prp ' \
                      '&& cat output/terminationAnalysisResult.txt)"'

                so = subprocess.getstatusoutput(cmd)
                out: str = so[1]

                if "Verification result: UNKNOWN" in out:
                    return False, main_function, None
                elif "Verification result: FALSE" in out:
                    print(out)
                    raise Exception("Unexpectedly non-terminating program:\n" + main_function)
                elif "Verification result: TRUE" in out:
                    try:
                        term_arg = out.split("Termination argument consisting of:")[1].strip().split("\n")

                        ranking_function = term_arg[0].replace("Ranking function ", "").replace("main::", "")
                        ranking_function = ranking_function\
                            .removeprefix(ranking_function.split(") = ")[0])\
                            .removeprefix(") = ")

                        invars = term_arg[1].replace("main::", "")\
                            .replace("Supporting invariants ", "")\
                            .replace("[", "")\
                            .replace("]","")\
                            .split(",")
                        if '' in invars:
                            invars.remove('')

                        if "-nested ranking function" in ranking_function:
                            print("Termination proved, but could only find a nested ranking function, "
                                  "I do not deal with this yet unfortunately for you..: " + str(ranking_function))
                            return True, None, None

                        return True, string_to_math_expression(ranking_function).simplify(), [string_to_prop(invar) for
                                                                                              invar in
                                                                             invars]
                    except Exception as err:
                        print("WARNING: Function terminates, but there is no ranking function, are you sure the loop has at least one iteration?")
                        return True, None, None
                else:
                    print(out)
                    raise Exception("Unexpected result during termination checking of:\n" + main_function)
            except subprocess.CalledProcessError as err:
                raise Exception(err.output + "\n\n" + out)
            finally:
                os.remove(tmp.name)
