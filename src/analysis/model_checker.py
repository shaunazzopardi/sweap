import logging
import os
import subprocess
import shutil
from tempfile import NamedTemporaryFile


class ModelChecker:
    def invar_check(self, nuxmv_script: str, ltl_spec, bound, mc):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            commands.write("go_msat\n")

            if not mc:
                call = 'check_invar_ic3 -i'
                call += ' -p "' + str(ltl_spec) + '"\n'

            if mc:
                call = 'check_ltlspec_ic3 -i'
                # if livenesstosafety != None and livenesstosafety:
                #     call += ' -K 0 '
                if bound is not None:
                    call += ' -k ' + str(bound)

                call += ' -p "' + str(ltl_spec) + '"\n'
            commands.write(call)
            commands.write('quit')
            commands.close()

            # cmd_exists = lambda x: shutil.which(x) is not None
            # if cmd_exists("nuxmv"):
            #     nuxmv_command = "nuxmv"
            # else:
            #     if cmd_exists("nuXmv"):
            #         nuxmv_command = "nuXmv"
            #     else:
            #         raise Exception("nuxmv is not in PATH")

            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")

                if "is true" in out:
                    return True, None
                elif "is false" in out:
                    return False, out
                elif "Maximum bound reached" in out:
                    return False, None
                else:
                    # TODO
                    return NotImplemented
            except subprocess.CalledProcessError as err:
                self.fail(err.output + "\n You may be using a special nuXmv keyword as a variable name.")
            finally:
                os.remove(model.name)
                os.remove(commands.name)

    def to_vmt(self, nuxmv_script: str, ltl_spec):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            if ltl_spec != None:
                model.write("LTLSPEC " + str(ltl_spec))
            model.close()

            commands.write("go_msat\n")
            commands.write("write_vmt_model -n 0 -o model.vmt\n")
            commands.write('quit\n')
            commands.close()

            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")
                logging.info(out)
            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(model.name)
                os.remove(commands.name)
