import logging

from pysmt.fnode import FNode
from pysmt.shortcuts import Solver, Interpolator, get_env, is_sat, serialize
from pysmt.solvers import solver


class SMTChecker:

    def __init__(self) -> None:
        self.solver = Solver(name="msat")
        # _add_solver(self.SOLVER_NAME, "msat")

    def check(self, smt: FNode):
        try:
            return self.solver.is_sat(smt)
        except Exception as e:
            self.solver = Solver(name="z3")
            return self.solver.is_sat(smt)


def binary_interpolant(A: FNode, B: FNode) -> FNode:
    with Interpolator(name="msat") as s:
        return s.binary_interpolant(A, B)


def check(smt: FNode):
    try:
        return is_sat(smt, solver_name="msat")
    except Exception as e:
        logging.info(serialize(smt))
        try:
            return is_sat(smt, solver_name="z3")
        except Exception as e:
            logging.info(serialize(smt))
            raise (e)
