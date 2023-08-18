from pysmt.fnode import FNode
from pysmt.shortcuts import Solver, Interpolator, get_env


class SMTChecker:
    SOLVER_NAME = "msat"

    # SOLVER_NAME = "mathsat-smtlib"

    def __init__(self) -> None:
        pass
        get_env().factory._get_available_solvers()
        # _add_solver(self.SOLVER_NAME, "msat")

    def check(self, smt: FNode):
        try:
            with Solver(name="msat") as s:
                return s.is_sat(smt)
        except:
            with Solver(name="z3") as s: # this is needed because msat does not support non-linear arithmetic
                return s.is_sat(smt)

    def binary_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        with Interpolator(name="msat") as s:
            return s.binary_interpolant(A, B)

    def sequence_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        # TODO
        pass
