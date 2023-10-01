import logging

from pysmt.fnode import FNode
from pysmt.shortcuts import Solver, Interpolator, is_sat, serialize


# class SMTChecker:
#
#     def __init__(self) -> None:
#         pass
#
#     def check(self, smt: FNode):
#         try:
#             solver = Solver(name="msat")
#             return solver.is_sat(smt)
#         except Exception as e:
#             solver = Solver(name="msat")
#             return solver.is_sat(smt)


def binary_interpolant(A: FNode, B: FNode) -> FNode:
    with Interpolator(name="msat") as s:
        return s.binary_interpolant(A, B)


def check(smt: FNode):
    try:
        return is_sat(smt, solver_name="msat")
    except Exception as e:
        # Sometimes the solver fails, probably due to parallelisation..
        logging.info(serialize(smt))
        try:
            return is_sat(smt, solver_name="msat")
        except Exception as e:
            logging.info(serialize(smt))
            raise (e)
