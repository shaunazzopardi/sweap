import logging
import os
import subprocess
from tempfile import NamedTemporaryFile

dirname = os.path.dirname(__file__)
nuxmv_path = str(os.path.join(dirname, "../../binaries/nuxmv"))


class ModelChecker:
    def invar_check(self, nuxmv_script: str, ltl_spec, bound, mc):
        with NamedTemporaryFile(
            "w", suffix=".smv", delete=False
        ) as model, NamedTemporaryFile("w", suffix=".txt", delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            commands.write("go_msat\n")

            if not mc:
                call = "check_invar_ic3 -i"
                call += ' -p "' + str(ltl_spec) + '"\n'
            else:
                call = "check_ltlspec_ic3 -i"
                # if livenesstosafety != None and livenesstosafety:
                #     call += ' -K 0 '
                if bound is not None:
                    call += " -k " + str(bound)

                call += ' -p "' + str(ltl_spec) + '"\n'

            commands.write(call)
            commands.write("quit")
            commands.close()

            try:
                out = subprocess.check_output(
                    [nuxmv_path, "-source", commands.name, model.name],
                    encoding="utf-8",
                )

                lower_out = out.lower()
                logging.info(out)

                if "is true" in lower_out:
                    return True, out
                elif "is false" in lower_out:
                    return False, out
                elif "maximum bound reached" in lower_out:
                    return False, out
                else:
                    raise Exception(
                        "Could not parse nuXmv result in ModelChecker.invar_check.\n"
                        "Expected output containing 'is true' or 'is false'.\n\n" + out
                    )
            except subprocess.CalledProcessError as err:
                raise Exception(err.output + "\n\n" + nuxmv_script)
            finally:
                os.remove(model.name)
                os.remove(commands.name)

    def to_vmt(self, nuxmv_script: str, ltl_spec, file: str):
        with NamedTemporaryFile(
            "w", suffix=".smv", delete=False
        ) as model, NamedTemporaryFile("w", suffix=".txt", delete=False) as commands:
            model.write(nuxmv_script)
            if ltl_spec != None:
                model.write("LTLSPEC " + str(ltl_spec))
            model.close()

            commands.write("go_msat\n")
            commands.write("write_vmt_model -n 0 -o " + file + ".vmt\n")
            commands.write("quit\n")
            commands.close()

            out = subprocess.check_output(
                [nuxmv_path, "-source", commands.name, model.name],
                encoding="utf-8",
            )
            logging.info(out)
            return out
