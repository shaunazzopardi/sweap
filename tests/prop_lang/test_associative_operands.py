import unittest

from prop_lang.biop import BiOp
from prop_lang.variable import Variable
from prop_lang.types.types import BOOLEAN


class TestAssociativeOperands(unittest.TestCase):
    def test_deep_chain_order_and_smt(self):
        variables = [Variable(f"operand_{i}") for i in range(2000)]
        formula = variables[0]
        for variable in variables[1:]:
            formula = BiOp(formula, "&", variable)
        self.assertEqual(formula.sub_formulas, variables)
        expr, invariant = formula.to_smt({v.name: BOOLEAN for v in variables})
        self.assertEqual(len(expr.args()), len(variables))
        self.assertTrue(invariant.is_true())
        self.assertEqual(str(formula), "(" + " & ".join(map(str, variables)) + ")")

    def test_mixed_operators_preserve_grouping(self):
        a, b, c = map(Variable, "abc")
        inner = BiOp(b, "|", c)
        formula = BiOp(a, "&", inner)
        self.assertEqual(formula.sub_formulas, [a, inner])
        self.assertEqual(BiOp(a, "->", b).sub_formulas[0].op, "->")

    def test_variable_order_and_duplicates(self):
        a, b, c = map(Variable, "abc")
        formula = BiOp(BiOp(b, "&", a), "|", BiOp(b, "&", c))
        self.assertEqual(formula.variablesin(), [b, a, c])
