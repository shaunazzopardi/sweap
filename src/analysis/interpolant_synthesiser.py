import os
import subprocess
from tempfile import NamedTemporaryFile

import pysmt.parsing
from pysmt.fnode import FNode

from programs.util import _add_solver, _check_os


class InterpolantSynthesiser:
    SOLVER_NAME = "cvc5"

    def __init__(self) -> None:
        _add_solver(self.SOLVER_NAME, self.SOLVER_NAME, [
            "--incremental",
            "--produce-interpolants", "--interpolants-mode=default",
            "--sygus-enum=fast", "--check-interpolants"])

    def interpolate(self, A: FNode, B: FNode):
        command = """
            ; COMMAND-LINE: --produce-interpolants --interpolants-mode=default --sygus-enum=fast --check-interpolants
            ; SCRUBBER: grep -v -E '(\(define-fun)'
            ; EXIT: 0\n""" + B.to_smtlib()

        # This stuff is not supported by pysmt, so we will inject it by hand
        logic = "(set-logic ALL)"
        interp = "(get-interpolant A " + A.to_smtlib() + ")"

        _check_os()

        with NamedTemporaryFile('w', suffix='.smt2', delete=False) as tmp:
            tmp.write(logic)
            tmp.write(command)
            tmp.write(interp)
            tmp.close()

            # Just some debug prints for when things go bad
            print(tmp.name)

            try:
                out = subprocess.check_output([
                    "cvc5", "--produce-interpolants",
                    "--interpolants-mode=default", "--sygus-enum=fast",
                    "--check-interpolants", tmp.name], encoding="utf-8")

                return pysmt.parsing.parse(out)

            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(tmp.name)
