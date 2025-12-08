from unittest import TestCase

from pysmt.shortcuts import And

from analysis.smt_checker import sequence_interpolant, binary_interpolant
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.types.types import INTEGER


class Test(TestCase):
    def test_sequence_interpolant(self):
        symbol_table = {}
        symbol_table["cnt_0"] = INTEGER
        symbol_table["cnt_1"] = INTEGER
        symbol_table["cnt_2"] = INTEGER
        symbol_table["cnt_3"] = INTEGER
        symbol_table["cnt_4"] = INTEGER

        formulas_str = [
            "cnt_0 = 0 & cnt_1 = cnt_0 + 1",
            "cnt_2 = cnt_1 + 1",
            "cnt_2 > 0 & cnt_3 = cnt_2 - 1",
            "cnt_3 > 0 & cnt_4 = cnt_3 - 1",
            "cnt_4 > 0",
        ]
        formulas_pr = list(map(string_to_prop, formulas_str))
        formulas = [And(*f.to_smt(symbol_table)) for f in formulas_pr]
        seq_interpolants = sequence_interpolant(formulas)

        self.assertTrue(len(seq_interpolants) >= 0)

        bin_interpolant1 = binary_interpolant(formulas[0], And(formulas[1:]))
        bin_interpolant2 = binary_interpolant(And(formulas[0:2]), And(formulas[2:]))
        bin_interpolant3 = binary_interpolant(And(formulas[0:3]), And(formulas[3:]))
        bin_interpolant4 = binary_interpolant(And(formulas[0:4]), And(formulas[4:]))

        self.assertTrue(
            set(seq_interpolants)
            == {bin_interpolant1, bin_interpolant2, bin_interpolant3, bin_interpolant4}
        )

    def test_sequence_interpolant2(self, simplify_formula_with=None):
        symbol_table = {}
        symbol_table["cnt_0"] = INTEGER
        symbol_table["cnt_1"] = INTEGER
        symbol_table["cnt_2"] = INTEGER
        symbol_table["cnt_3"] = INTEGER
        symbol_table["cnt_4"] = INTEGER

        formulas_str = [
            "cnt_0 = 0 & cnt_1 = cnt_0 + 1",
            "cnt_2 = cnt_1 + 1",
            "cnt_2 > 0 & cnt_3 = cnt_2 - 1",
            "cnt_3 > 0 & cnt_4 = cnt_3 - 1",
            "cnt_4 > 0",
        ]

        formulas_pr = list(map(string_to_prop, formulas_str))
        formulas = [And(*f.to_smt(symbol_table)) for f in formulas_pr]
        seq_interpolants = sequence_interpolant(formulas)

        self.assertTrue(len(seq_interpolants) >= 0)

        bin_interpolant1 = binary_interpolant(formulas[0], And(formulas[1:]))
        bin_interpolant2 = binary_interpolant(And(formulas[0:2]), And(formulas[2:]))
        bin_interpolant3 = binary_interpolant(And(formulas[0:3]), And(formulas[3:]))
        bin_interpolant4 = binary_interpolant(And(formulas[0:4]), And(formulas[4:]))

        self.assertTrue(
            set(seq_interpolants)
            == {bin_interpolant1, bin_interpolant2, bin_interpolant3, bin_interpolant4}
        )
