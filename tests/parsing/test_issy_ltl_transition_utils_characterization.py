import unittest

from parsing.string_to_ltl import string_to_issy_ltl
from parsing.util.issy.reductions.transition_utils import (
    _rewrite_x_candidates_to_primed,
)
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestIssyLtlTransitionUtilsCharacterization(unittest.TestCase):
    def test_rewrite_x_candidates_handles_parser_math_expr(self):
        # Parser emits MathExpr under X for arithmetic relations.
        parsed = string_to_issy_ltl("X((x <= 0))")
        self.assertIsInstance(parsed, UniOp)
        self.assertIsInstance(parsed.right, MathExpr)

        rewritten_from_parser = _rewrite_x_candidates_to_primed(parsed, {"x"})
        rewritten_from_raw_biop = _rewrite_x_candidates_to_primed(
            UniOp("X", BiOp(Variable("x"), "<=", Value("0"))),
            {"x"},
        )

        # Both parsed MathExpr and raw BiOp paths should rewrite x -> x'.
        self.assertEqual(str(rewritten_from_parser), "(x' <= 0)")
        self.assertEqual(str(rewritten_from_raw_biop), "(x' <= 0)")


if __name__ == "__main__":
    unittest.main()
