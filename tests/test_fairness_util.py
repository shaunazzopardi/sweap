from unittest import TestCase

from analysis.refinement.fairness_refinement.fairness_util import function_has_well_ordered_range, \
    function_decreases_in_loop_body
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_function_has_well_ordered_range(self):
        symbol_table = {"x": TypedValuation("x", "nat", "0")}
        symbol_table |= {"x_prev": TypedValuation("x_prev", "nat", "0")}
        formula = Variable("x")

        result = function_has_well_ordered_range(formula, [], symbol_table)
        self.assertTrue(result)


class Test(TestCase):
    def test_function_decreases_in_loop_body(self):
        symbol_table = {"x": TypedValuation("x", "nat", "0")}
        symbol_table |= {"x_prev": TypedValuation("x_prev", "nat", "0")}
        x = Variable("x")
        body = [BiOp(x, ":=", BiOp(x, "+", Value("1")))]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(not result)

    def test_function_decreases_in_loop_body1(self):
        symbol_table = {"x": TypedValuation("x", "nat", "0")}
        symbol_table |= {"x_prev": TypedValuation("x_prev", "nat", "0")}
        x = Variable("x")
        body = [BiOp(x, ":=", BiOp(x, "-", Value("1")))]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)

    def test_function_decreases_in_loop_body2(self):
        symbol_table = {"x": TypedValuation("x", "nat", "0")}
        symbol_table |= {"x_prev": TypedValuation("x_prev", "nat", "0")}
        x = Variable("x")
        body = [BiOp(x, ":=", BiOp(x, "-", x))]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)

    def test_liveness_step(self):
        local_vars = [Variable("cnt")]

        symbol_table = {"cnt": TypedValuation("cnt", "nat", Value("0"))}
        prefix = None

        self.fail()
