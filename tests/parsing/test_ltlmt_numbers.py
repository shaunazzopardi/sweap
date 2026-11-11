from pathlib import Path
from unittest import TestCase

from parsing.string_to_ltl import (
    Semantics,
    parser_ltl,
    parser_ltlmt,
    string_to_ltlmt,
)


class TestLtlmtNumbers(TestCase):
    def test_integer_literal_prefixes_and_signs(self):
        for token, expected in (
            ("i0()", "0"), ("i7()", "7"), ("i10000()", "10000"),
            ("im12()", "-12"), ("c25()", "25"), ("cm50()", "-50"),
        ):
            with self.subTest(token=token):
                value = parser_ltlmt.parse(
                    token, start="number_ltlmt", semantics=Semantics()
                )
                self.assertEqual(str(value), expected)

    def test_plain_integer_tokens_preserve_signs_and_all_digits(self):
        for token in ("0", "12345", "-12345"):
            with self.subTest(token=token):
                value = parser_ltl.parse(
                    token, start="number_ltl", semantics=Semantics()
                )
                self.assertEqual(str(value), token)

    def test_numeric_literals_in_complete_formula(self):
        parsed, declarations = string_to_ltlmt(
            "guarantee { [x <- im12()]; G (gt x i10000()); }"
        )
        self.assertEqual(declarations, {})
        self.assertEqual(str(parsed[0][2][0][0]), "x := -12")
        self.assertEqual(str(parsed[0][2][1][0]), "G((x > 10000))")

    def test_failing_benchmark_parses(self):
        path = (
            Path(__file__).resolve().parents[2]
            / "benchmarks/tslmt2rpg/f-unreal.tslmt"
        )
        parsed, declarations = string_to_ltlmt(path.read_text())
        self.assertEqual(declarations["e"], ("inp", "Int"))
        expressions = [str(statement[0]) for macro in parsed for statement in macro[2]]
        self.assertTrue(any("10000" in expression for expression in expressions))
