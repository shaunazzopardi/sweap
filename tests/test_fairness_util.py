from unittest import TestCase

from analysis.refinement.fairness_refinement.fairness_util import (
    function_has_well_ordered_range,
    function_decreases_in_loop_body,
    _normalise_exit_condition_for_liveness,
)
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.types.types import NATURAL
from prop_lang.biop import BiOp
from prop_lang.update import Update
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_function_has_well_ordered_range(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        formula = Variable("x")

        result = function_has_well_ordered_range(formula, [], symbol_table)
        self.assertTrue(result)


class Test(TestCase):
    def test_function_decreases_in_loop_body(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "+", Value(1)))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(not result)

    def test_function_decreases_in_loop_body1(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "-", Value(1)))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)

    def test_function_decreases_in_loop_body2(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "-", x))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)


class TestPrevNormalisation(TestCase):
    class _DummyProgram:
        env_events = []
        con_events = []
        out_events = []

    def test_normalise_exit_condition_grounds_prev_refs(self):
        exit_cond = string_to_prop("(x < x_prev) & (z_prev < z)")
        valuation = {"x_prev": "2", "z_prev": "0"}

        normalised = _normalise_exit_condition_for_liveness(
            self._DummyProgram(), exit_cond, valuation, {}
        )

        self.assertFalse(any("_prev" in str(v) for v in normalised.variablesin()))
        self.assertIn("x", str(normalised))
        self.assertIn("z", str(normalised))

    def test_normalise_exit_condition_with_full_prev_valuation(self):
        exit_cond = string_to_prop("(x < x_prev) & (z_prev < z)")
        valuation = {"x_prev": "5", "z_prev": "1"}

        normalised = _normalise_exit_condition_for_liveness(
            self._DummyProgram(), exit_cond, valuation, {}
        )

        self.assertFalse(any("_prev" in str(v) for v in normalised.variablesin()))
