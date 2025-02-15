from unittest import TestCase

import pysmt
from pysmt.shortcuts import And, Solver, serialize, to_smtlib, Symbol, Exists, ForAll, Implies
from pysmt.typing import INT

from analysis.smt_checker import sequence_interpolant, binary_interpolant, quantifier_elimination
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.types.types import INTEGER
from prop_lang.util import neg, conjunct, fnode_to_formula
from prop_lang.value import Value


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


    def test_qe(self):
        p0 = string_to_prop("(c_1 = c_0) & (e_1 = set_e) & (c_0 = 0) & (e_0 = 0)")
        p1 = string_to_prop("!((c_1 + -e_1) < (c_0 + -e_0))")

        symbol_table = {
                        "e_0" : TypedValuation("e_0", "int", None),
                        "e_1" : TypedValuation("e_1", "int", None),
                        "c_0" : TypedValuation("c_0", "int", None),
                        "c_1" : TypedValuation("c_1", "int", None),
                        "set_e": TypedValuation("set_e", "int", None)
        }

        exist_vars = [Symbol("e_0", INT), Symbol("c_0", INT), Symbol("set_e", INT)]
        forall_vars = [Symbol("c_1", INT), Symbol("e_1", INT)]
        quant_formula = Exists(exist_vars,
                               ForAll(forall_vars, Implies(p0.to_smt(symbol_table)[0], p1.to_smt(symbol_table)[0])))

        ret = quantifier_elimination(quant_formula)
        rett = fnode_to_formula(ret)
        print()