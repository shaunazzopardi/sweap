"""
Tests for extracting initial-state formulas and fixed initial values.
"""

import unittest
import re

from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.types.values import BoolAtoms
from prop_lang.util import extract_initial_values, disjunct
from parsing.string_to_ltl import string_to_issy_ltl


class TestExtractInitialValues(unittest.TestCase):
    def setUp(self):
        self.var_x = Variable("x")
        self.var_p = Variable("p")
        self.var_q = Variable("q")
        self.symbol_table = {
            "x": INTEGER,
            "p": BOOLEAN,
            "q": BOOLEAN,
        }

    def _extract_formula_line(self, path: str, prefix: str) -> str:
        with open(path, "r") as handle:
            for line in handle:
                stripped = line.strip()
                if not stripped.startswith(prefix):
                    continue
                formula = stripped[len(prefix) :].strip()
                formula = re.sub(r"//.*$", "", formula).strip()
                if formula.endswith(";"):
                    formula = formula[:-1].strip()
                return formula
        raise AssertionError(f"no line starting with {prefix} in {path}")

    def test_propositional_formula_returns_self_and_fixed_bool(self):
        init_formula, fixed = extract_initial_values(
            {self.var_p}, self.var_p, self.symbol_table
        )
        self.assertEqual(init_formula, self.var_p)
        self.assertEqual(fixed[self.var_p], Value(BoolAtoms.TRUE))

    def test_until_initial_formula(self):
        formula = BiOp(self.var_p, "U", self.var_q)
        init_formula, fixed = extract_initial_values(
            {self.var_p, self.var_q}, formula, self.symbol_table
        )
        self.assertEqual(init_formula, disjunct(self.var_p, self.var_q))
        self.assertEqual(fixed, {})

    def test_global_equality_on_infinite_domain(self):
        formula = UniOp("G", BiOp(self.var_x, "=", Value(0)))
        init_formula, fixed = extract_initial_values(
            {self.var_x}, formula, self.symbol_table
        )
        self.assertEqual(init_formula, BiOp(self.var_x, "=", Value(0)))
        self.assertEqual(fixed[self.var_x], Value(0))

    def test_eventually_has_no_initial_constraints(self):
        formula = UniOp("F", self.var_p)
        init_formula, fixed = extract_initial_values(
            {self.var_p}, formula, self.symbol_table
        )
        self.assertIsNone(init_formula)
        self.assertEqual(fixed, {})

    def test_balancer_guard_initial_formula(self):
        path = "/home/shaun-azzopardi/Projects/Playground/sweap/benchmarks/issy/balancers/balancer.issy"
        formula_text = self._extract_formula_line(path, "assert G (r0'")
        formula_text = "G (r0' " + formula_text
        formula = string_to_issy_ltl(formula_text)
        init_formula, fixed = extract_initial_values(
            {Variable("r0'"), Variable("x0"), Variable("i0")},
            formula,
            {"r0'": BOOLEAN, "x0": INTEGER, "i0": INTEGER},
        )
        self.assertEqual(init_formula, formula.right)
        self.assertEqual(fixed, {})

    def test_balancer_initial_values_assumption(self):
        path = "/home/shaun-azzopardi/Projects/Playground/sweap/benchmarks/issy/balancers/balancer.issy"
        formula_text = self._extract_formula_line(path, "assume ([x0")
        formula_text = "([x0 " + formula_text
        formula = string_to_issy_ltl(formula_text)
        init_formula, fixed = extract_initial_values(
            {
                Variable("x0"),
                Variable("x1"),
                Variable("y0"),
                Variable("y1"),
                Variable("sumin"),
            },
            formula,
            {
                "x0": INTEGER,
                "x1": INTEGER,
                "y0": INTEGER,
                "y1": INTEGER,
                "sumin": INTEGER,
            },
        )
        self.assertEqual(init_formula, formula)
        self.assertEqual(fixed[Variable("x0")], Value(0))
        self.assertEqual(fixed[Variable("sumin")], Value(0))

    def test_until_with_weak_until_from_benchmark(self):
        path = "/home/shaun-azzopardi/Projects/Playground/sweap/benchmarks/issy/test-11.issy"
        formula_text = self._extract_formula_line(path, "assert G (")
        formula_text = "G (" + formula_text
        formula = string_to_issy_ltl(formula_text)
        init_formula, fixed = extract_initial_values(
            {Variable("start"), Variable("stop"), Variable("x")},
            formula,
            {"start": BOOLEAN, "stop": BOOLEAN, "x": INTEGER},
        )
        self.assertIsNone(init_formula)
        self.assertEqual(fixed, {})


if __name__ == "__main__":
    unittest.main()
