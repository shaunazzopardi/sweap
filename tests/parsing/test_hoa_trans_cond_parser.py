from unittest import TestCase

from parsing.hoa_parser import hoa_trans_cond_parser
from prop_lang.biop import BiOp
from prop_lang.util import false, neg, true
from prop_lang.variable import Variable


class TestHoaTransCondParser(TestCase):
    def test_precedence_and_negation(self):
        cond = "0 & !1 | 2"
        expected = BiOp(
            BiOp(Variable("0"), "&", neg(Variable("1"))),
            "|",
            Variable("2"),
        )
        self.assertEqual(hoa_trans_cond_parser(cond), expected)

    def test_parentheses_override(self):
        cond = "!(0 | 1) & 2"
        expected = BiOp(
            neg(BiOp(Variable("0"), "|", Variable("1"))),
            "&",
            Variable("2"),
        )
        self.assertEqual(hoa_trans_cond_parser(cond), expected)

    def test_double_symbol_operators(self):
        cond = "a && (!b || c)"
        expected = BiOp(
            Variable("a"),
            "&",
            BiOp(neg(Variable("b")), "|", Variable("c")),
        )
        self.assertEqual(hoa_trans_cond_parser(cond), expected)

    def test_boolean_constants(self):
        cond = "t | f & 1"
        expected = BiOp(true(), "|", BiOp(false(), "&", Variable("1")))
        self.assertEqual(hoa_trans_cond_parser(cond), expected)
