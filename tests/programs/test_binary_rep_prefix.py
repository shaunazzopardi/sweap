from unittest import TestCase
from unittest.mock import patch

from pysmt.shortcuts import Iff, Not, Or, is_sat
from programs.binary_rep_map import BinaryRepMap
from prop_lang.types.types import BOOLEAN
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, neg, true
from prop_lang.variable import Variable


class TestBinaryRepPrefix(TestCase):
    def test_prefixes_match_explicit_code_disjunctions(self):
        differences = []
        for size in range(1, 66):
            # Nonconsecutive labels also model the surviving, inhabited cells
            # after type-domain pruning. Encoding follows their list order.
            keys = [Variable(f"cell_{3 * i + 7}") for i in range(size)]
            bits, encoding = BinaryRepMap.build_binary_rep(keys, "prefix_bit_")
            symbols = {str(bit): BOOLEAN for bit in bits}
            for count in range(size + 1):
                expected = (
                    true() if count == size
                    else disjunct_formula_set(encoding[key] for key in keys[:count])
                )
                actual = encoding.prefix_disjunction(count)
                differences.append(Not(Iff(
                    expected.to_smt(symbols)[0], actual.to_smt(symbols)[0],
                )))
        self.assertFalse(is_sat(Or(differences), solver_name="z3"))

    def test_prefix_construction_does_not_normalise_boolean_formulas(self):
        with patch(
            "programs.binary_rep_map.dnf_safe",
            side_effect=AssertionError("unexpected DNF normalization"),
        ):
            _, encoding = BinaryRepMap.build_binary_rep(list(range(60)), "prefix_bit_")
            for count in range(61):
                encoding.prefix_disjunction(count)

    def test_factory_codes_match_explicit_binary_values(self):
        differences = []
        for size in range(2, 66):
            bits, encoding = BinaryRepMap.build_binary_rep(list(range(size)), "code_")
            symbols = {str(bit): BOOLEAN for bit in bits}
            exact_codes = [
                conjunct_formula_set([
                    bit if digit == "1" else neg(bit)
                    for bit, digit in zip(bits, format(value, f"0{len(bits)}b"))
                ])
                for value in range(2 ** len(bits))
            ]
            for index, representation in encoding.items():
                expected = (
                    exact_codes[index] if index < size - 1
                    else disjunct_formula_set(exact_codes[index:])
                )
                differences.append(Not(Iff(
                    expected.to_smt(symbols)[0], representation.to_smt(symbols)[0],
                )))
        self.assertFalse(is_sat(Or(differences), solver_name="z3"))

    def test_single_inhabited_cell_needs_no_bits(self):
        encoding = BinaryRepMap({Variable("only_cell"): true()}, bin_vars=[])
        self.assertTrue(encoding.prefix_disjunction(0).is_false())
        self.assertTrue(encoding.prefix_disjunction(1).is_true())

    def test_invalid_prefix_length(self):
        _, encoding = BinaryRepMap.build_binary_rep(["first", "last"], "prefix_bit_")
        for count in (-1, 3):
            with self.subTest(count=count), self.assertRaises(ValueError):
                encoding.prefix_disjunction(count)
