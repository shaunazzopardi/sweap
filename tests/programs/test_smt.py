import os
import shutil
import subprocess
from tempfile import NamedTemporaryFile
from unittest import SkipTest, TestCase

from pysmt.factory import SolverRedefinitionError
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import Solver, Symbol, get_env

from programs.typed_valuation import TypedValuation
from parsing.string_to_ltl import string_to_ltl


def _check_os():
    if os.name not in ("posix", "nt"):
        raise SkipTest(f"This test does not support OS '{os.name}'.")


def _add_solver(description, command, args=[], logics=None):
    _check_os()
    logics = logics or [QF_UFLRA]

    path = shutil.which(command)

    # Add the solver to the environment
    env = get_env()
    try:
        env.factory.add_generic_solver(description, [path, *args], logics)
    except SolverRedefinitionError:
        # Solver has already been registered, skip
        pass


class TestCvc5(TestCase):
    SOLVER_NAME = "cvc5"

    def __init__(self, methodName: str = ...) -> None:
        super().__init__(methodName)
        _add_solver(self.SOLVER_NAME, self.SOLVER_NAME, [
            "--incremental",
            "--produce-interpolants", "--interpolants-mode=default",
            "--sygus-enum=fast", "--check-interpolants"])

    def test_solver(self):
        """Tests that the solver works
        """
        _check_os()
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertTrue(s.is_sat(Symbol("x")))

    def test_interpolation(self):
        """Compute an interpolant using CVC5

        Sources:
        https://github.com/cvc5/cvc5/blob/main/test/regress/cli/regress1/sygus/interpol_arr1.smt2 (example)
        https://pysmt.readthedocs.io/en/latest/tutorials.html?highlight=declare#demonstrates-how-to-perform-smt-lib-parsing-dumping-and-extension (SMT-LIB parsing)
        """

        # For the sake of this demo, we just take an example from CVC5's repo,
        # parse and unparse it. In the actual code we will generate formulae
        # with the pysmt API and then use the serialize() method to get the
        # SMT-LIB code
        example = """
        ; COMMAND-LINE: --produce-interpolants --interpolants-mode=default --sygus-enum=fast --check-interpolants
        ; SCRUBBER: grep -v -E '(\(define-fun)'
        ; EXIT: 0
        (declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
        (declare-fun y () (_ BitVec 4))
        (assert (= (select a y) (_ bv0 4)))
        """
        # parser = SmtLibParser()
        # script = parser.get_script(StringIO(example))

        # This stuff is not supported by pysmt, so we will inject it by hand
        logic = "(set-logic ALL)"
        interp = "(get-interpolant A (distinct (select a y) (_ bv1 4)))"

        _check_os()

        with NamedTemporaryFile('w', suffix='.smt2', delete=False) as tmp:
            tmp.write(logic)
            # script.serialize(tmp, daggify=True)
            tmp.write(example)
            tmp.write(interp)
            tmp.close()

            # Just some debug prints for when things go bad
            print(tmp.name)

            try:
                out = subprocess.check_output([
                    "cvc5", "--produce-interpolants",
                    "--interpolants-mode=default", "--sygus-enum=fast",
                    "--check-interpolants", tmp.name], encoding="utf-8")

                # out should contain "(define-fun A () Bool (not (= (select a y) #b0001)))"
                print("output:", out)
                self.assertIn("define-fun", out)

            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(tmp.name)


class TestMathSat(TestCase):
    SOLVER_NAME = "mathsat-smtlib"

    # def _add_mathsat(self):
    #     _check_os()

    #     msat_path = shutil.which("mathsat")

    #     # Add the solver to the environment
    #     env = get_env()
    #     try:
    #         env.factory.add_generic_solver(self.SOLVER_NAME, [msat_path], [QF_UFLRA])
    #     except SolverRedefinitionError:
    #         # Solver has already been registered, skip
    #         pass

    # def _check_os(self):
    #     if os.name not in ("posix", "nt"):
    #         raise SkipTest(f"This test does not support OS '{os.name}'.")

    def __init__(self, methodName: str = ...) -> None:
        super().__init__(methodName)
        _add_solver(self.SOLVER_NAME, "mathsat")

    def test_mathsat(self):
        """Tests that a system-wide mathsat can be found and driven by pysmt
        """
        _check_os()
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertTrue(s.is_sat(Symbol("x")))

    def _test_to_smt(self, ltl_str: str, symbols: dict, expected_sat: bool):
        _check_os()
        ltl = string_to_ltl(ltl_str)
        smt = ltl.to_smt(symbols)
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertEqual(s.is_sat(smt), expected_sat)

    def test_to_smt_0(self):
        self._test_to_smt("1 == 0", {}, False, )

    def test_to_smt_1(self):
        self._test_to_smt(
            "TO_BE || (!TO_BE)",
            {"TO_BE": TypedValuation("TO_BE", "bool", True)},
            True)

    def test_to_smt_2(self):
        self._test_to_smt(
            "TO_BE && (!TO_BE)",
            {"TO_BE": TypedValuation("TO_BE", "bool", True)},
            False)

    def test_to_smt_3(self):
        self._test_to_smt(
            "(ROOMCLEAN && (!INROOM) && (! DOORLOCKED))",
            {
                "ROOMCLEAN": TypedValuation("ROOMCLEAN", "bool", True),
                "INROOM": TypedValuation("INROOM", "bool", True),
                "DOORLOCKED": TypedValuation("DOORLOCKED", "bool", True)
            },
            True)
