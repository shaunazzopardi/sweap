import logging

from pysmt.fnode import FNode
from pysmt.shortcuts import Interpolator, is_sat, serialize, qelim
from pysmt.simplifier import BddSimplifier


def binary_interpolant(A: FNode, B: FNode) -> FNode:
    with Interpolator(name="msat") as s:
        return s.binary_interpolant(A, B)


def sequence_interpolant(formulas: [FNode]) -> [FNode]:
    with Interpolator(name="msat") as s:
        return s.sequence_interpolant(formulas)


def quantifier_elimination(formula: FNode) -> FNode:
    return qelim(formula, solver_name="z3")


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


def bdd_simplify(f: FNode):
    try:
        s = BddSimplifier()
        fprime = s.simplify(f)
        return fprime
    except Exception as e:
        print(e)


