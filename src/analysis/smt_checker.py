import logging

from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.rewritings import conjunctive_partition
from pysmt.shortcuts import (
    Interpolator,
    get_unsat_core,
    is_sat,
    serialize,
    qelim,
    Solver,
)
from pysmt.simplifier import BddSimplifier


def binary_interpolant(A: FNode, B: FNode) -> FNode:
    with Interpolator(name="msat") as s:
        return s.binary_interpolant(A, B)


def sequence_interpolant(formulas: [FNode]) -> [FNode]:
    with Interpolator(name="msat") as s:
        return s.sequence_interpolant(formulas)


def quantifier_elimination(formula: FNode) -> FNode:
    return qelim(formula, solver_name="z3")


def find_unsat_core(smt: FNode):
    return get_unsat_core(conjunctive_partition(smt))


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


def bdd_simplify(f: FNode, static_ordering=None, bool_abstraction=True):
    try:
        s = BddSimplifier(
            static_ordering=static_ordering, bool_abstraction=bool_abstraction
        )
        fprime = s.simplify(f)
        return fprime
    except Exception as e:
        if "not available" in str(e):
            print("BDD solver not installed in pysmt. BDD simplification disabled.")
        else:
            print(e)
        return None
