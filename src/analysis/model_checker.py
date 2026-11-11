import logging
import os
import re
import subprocess
from tempfile import NamedTemporaryFile

dirname = os.path.dirname(__file__)
nuxmv_path = str(os.path.join(dirname, "../../binaries/nuxmv"))


class ModelChecker:
    def invar_check(self, modules: dict[str, str], ltl_spec, bound, mc):
        """Check a property in main; each mapping value is one complete module."""
        if "main" not in modules:
            raise ValueError("nuXmv model has no main module")
        nuxmv_script = "\n".join(modules.values())
        property_name = "__sweap_check"
        while re.search(r"\b" + property_name + r"\b", nuxmv_script):
            property_name += "_"
        property_type = "LTLSPEC" if mc else "INVARSPEC"
        # Keep large properties out of the command interpreter's quoted -p
        # argument. Add the property while rendering, without changing the model.
        property_text = f"\n{property_type} NAME {property_name} := {ltl_spec};\n"
        nuxmv_script = "\n".join(
            text + property_text if name == "main" else text
            for name, text in modules.items()
        )
        with NamedTemporaryFile(
            "w", suffix=".smv", delete=False
        ) as model, NamedTemporaryFile("w", suffix=".txt", delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            # Abort script errors rather than returning to an interactive
            # prompt, where a benchmark worker can mistake them for timeouts.
            commands.write("set on_failure_script_quits\ngo_msat\n")

            if not mc:
                call = "check_invar_ic3 -i"
            else:
                call = "check_ltlspec_ic3 -i"
                # if livenesstosafety != None and livenesstosafety:
                #     call += ' -K 0 '
                if bound is not None:
                    call += " -k " + str(bound)

            call += " -P " + property_name + "\n"

            commands.write(call)
            commands.write("quit")
            commands.close()

            try:
                out = subprocess.check_output(
                    [nuxmv_path, "-source", commands.name, model.name],
                    encoding="utf-8",
                    stdin=subprocess.DEVNULL,
                    stderr=subprocess.STDOUT,
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
                raise RuntimeError(
                    f"nuXmv failed (exit {err.returncode}):\n{err.output}"
                ) from err
            finally:
                os.remove(model.name)
                os.remove(commands.name)

    def to_vmt(self, modules: dict[str, str], ltl_spec, file: str):
        modules = dict(modules)
        if ltl_spec is not None:
            modules["main"] += "\nLTLSPEC " + str(ltl_spec) + ";\n"
        with NamedTemporaryFile(
            "w", suffix=".smv", delete=False
        ) as model, NamedTemporaryFile("w", suffix=".txt", delete=False) as commands:
            model.write("\n".join(modules.values()))
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
