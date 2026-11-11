import unittest

from prop_lang.biop import BiOp
from prop_lang.value import Value
from prop_lang.variable import Variable
from prop_lang.types.types import INTEGER


class TestValueAndStrix(unittest.TestCase):
    def test_nested_strix_formula(self):
        formula = BiOp(Variable("a"), "&", BiOp(Variable("b"), "|", Variable("c")))
        self.assertEqual(formula.to_strix(), "(a) & ((b) | (c))")

    def test_signed_integer_values(self):
        for value in [-12, -1, 0, 12]:
            with self.subTest(value=value):
                literal = Value(value)
                self.assertTrue(literal.is_math_value())
                self.assertEqual(literal.type(), INTEGER)
                self.assertEqual(literal.to_smt({})[0].constant_value(), value)

    def test_invalid_integer_values(self):
        for value in ["12junk", "1.5", "-", ""]:
            with self.subTest(value=value):
                literal = Value(value)
                self.assertFalse(literal.is_math_value())
                with self.assertRaisesRegex(Exception, "not a boolean or integer"):
                    literal.type()
