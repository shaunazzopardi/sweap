from unittest import TestCase

from prop_lang.factory import _mult
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestFactory(TestCase):
    def test_mult_accepts_unary_negative_constant_with_variable(self):
        result = _mult(UniOp("-", Value(2)), Variable("x"))
        self.assertIsInstance(result, UniOp)
        self.assertEqual(result.op, "-")

    def test_mult_constant_product_keeps_negative_as_unary_op(self):
        result = _mult(UniOp("-", Value(2)), Value(3))
        self.assertIsInstance(result, UniOp)
        self.assertEqual(result.op, "-")
        self.assertIsInstance(result.right, Value)
        self.assertEqual(int(result.right.val), 6)

