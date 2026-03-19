from unittest import TestCase
from unittest.mock import patch

from analysis.refinement.fairness_refinement.fairness_util import (
    function_has_well_ordered_range,
    function_decreases_in_loop_body,
    try_liveness_refinement,
)
from config import Config
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

    class _DummyPredicateAbstraction:
        @staticmethod
        def get_symbol_table():
            return {}

    def test_skips_liveness_refinement_on_prev_mismatch(self):
        conf = Config.getConfig()
        old_only_safety = conf.only_safety
        conf.only_safety = False

        try:
            with patch(
                "analysis.refinement.fairness_refinement.fairness_util.use_fairness_refinement"
            ) as fairness_check, patch(
                "analysis.refinement.fairness_refinement.fairness_util.liveness_step"
            ) as liveness_step:
                success, result = try_liveness_refinement(
                    Cs=None,
                    program=None,
                    predicate_abstraction=self._DummyPredicateAbstraction(),
                    agreed_on_execution=[],
                    disagreed_on_state=([string_to_prop("x_prev < x")], None),
                    signatures={},
                    loop_counter=0,
                    allow_user_input=False,
                )

            self.assertFalse(success)
            self.assertIsNone(result)
            fairness_check.assert_not_called()
            liveness_step.assert_not_called()
        finally:
            conf.only_safety = old_only_safety
