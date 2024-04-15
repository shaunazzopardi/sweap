from unittest import TestCase

import pysmt
from pysmt.shortcuts import And, Solver, serialize, to_smtlib

from analysis.smt_checker import sequence_interpolant, binary_interpolant
from parsing.string_to_prop_logic import string_to_prop
from programs.typed_valuation import TypedValuation
from prop_lang.util import neg
from prop_lang.value import Value


class Test(TestCase):
    def test_sequence_interpolant(self):
        symbol_table = {}
        symbol_table["cnt_0"] = TypedValuation("cnt_0", "int", 0)
        symbol_table["cnt_1"] = TypedValuation("cnt_1", "int", 0)
        symbol_table["cnt_2"] = TypedValuation("cnt_2", "int", 0)
        symbol_table["cnt_3"] = TypedValuation("cnt_3", "int", 0)
        symbol_table["cnt_4"] = TypedValuation("cnt_4", "int", 0)

        formulas_str = ["cnt_0 = 0 & cnt_1 = cnt_0 + 1",
                        "cnt_2 = cnt_1 + 1",
                        "cnt_2 > 0 & cnt_3 = cnt_2 - 1",
                        "cnt_3 > 0 & cnt_4 = cnt_3 - 1",
                        "cnt_4 > 0"
                        ]
        formulas_pr = list(map(string_to_prop, formulas_str))
        formulas = [And(*f.to_smt(symbol_table)) for f in formulas_pr]
        seq_interpolants = sequence_interpolant(formulas)

        self.assertTrue(len(seq_interpolants) >= 0)

        bin_interpolant1 = binary_interpolant(formulas[0], And(formulas[1:]))
        bin_interpolant2 = binary_interpolant(And(formulas[0:2]), And(formulas[2:]))
        bin_interpolant3 = binary_interpolant(And(formulas[0:3]), And(formulas[3:]))
        bin_interpolant4 = binary_interpolant(And(formulas[0:4]), And(formulas[4:]))

        self.assertTrue(set(seq_interpolants) == {bin_interpolant1, bin_interpolant2, bin_interpolant3,
                                                  bin_interpolant4})

    def test_sequence_interpolant2(self, simplify_formula_with=None):
        symbol_table = {}
        symbol_table["cnt_0"] = TypedValuation("cnt_0", "int", 0)
        symbol_table["cnt_1"] = TypedValuation("cnt_1", "int", 0)
        symbol_table["cnt_2"] = TypedValuation("cnt_2", "int", 0)
        symbol_table["cnt_3"] = TypedValuation("cnt_3", "int", 0)
        symbol_table["cnt_4"] = TypedValuation("cnt_4", "int", 0)

        formulas_str = ["cnt_0 = 0 & cnt_1 = cnt_0 + 1",
                        "cnt_2 = cnt_1 + 1",
                        "cnt_2 > 0 & cnt_3 = cnt_2 - 1",
                        "cnt_3 > 0 & cnt_4 = cnt_3 - 1",
                        "cnt_4 > 0"
                        ]

        formulas_pr = list(map(string_to_prop, formulas_str))
        formulas = [And(*f.to_smt(symbol_table)) for f in formulas_pr]
        seq_interpolants = sequence_interpolant(formulas)

        self.assertTrue(len(seq_interpolants) >= 0)

        bin_interpolant1 = binary_interpolant(formulas[0], And(formulas[1:]))
        bin_interpolant2 = binary_interpolant(And(formulas[0:2]), And(formulas[2:]))
        bin_interpolant3 = binary_interpolant(And(formulas[0:3]), And(formulas[3:]))
        bin_interpolant4 = binary_interpolant(And(formulas[0:4]), And(formulas[4:]))

        self.assertTrue(set(seq_interpolants) == {bin_interpolant1, bin_interpolant2, bin_interpolant3,
                                                  bin_interpolant4})

    def test_print_util(self):
        s = ""
        for i in range(0, 51):
            s += "(G F (at_floor == " + str(i) + ")) && "

        print(s)
        self.assertTrue(True)

    def test_must(self):
        words = "(x0_prev > x0), (((x0 - x1) + (y0 - y1)) <= 2), (0 <= (x1 - x0)), (2 <= ((x0 - x1) + (y0 - y1))), (x0 <= 0), (x0 >= 0), (x1_prev < x1), (0 <= (y0 - y1)), (x1 <= 0), (2 <= ((x1 - x0) + (y0 - y1))), (0 <= (y1 - y0)), (2 <= ((x1 - x0) + (y1 - y0))), (y1 <= 0), (y1_prev > y1), (((x1 - x0) + (y1 - y0)) <= 2), (0 <= (x0 - x1)), (y1_prev < y1), (x0_prev < x0), (y0_prev > y0), (x1 >= 0), (((x0 - x1) + (y1 - y0)) <= 2), (((x1 - x0) + (y0 - y1)) <= 2), (y1 >= 0), (y0 <= 0), (2 <= ((x0 - x1) + (y1 - y0))), (y0 >= 0), (y0_prev < y0), (x1_prev > x1)"

        words = words.split(", ")
        props = list(map(string_to_prop, words))
        props += [neg(p) for p in props]

        symbol_table = {str(v): TypedValuation(str(v), "int", Value("0")) for p in props for v in p.variablesin()}
        smt_lib = ""
        vars = set("(declare-const " + str(v) + " Int)" for p in props for v in p.variablesin())

        with Solver() as solver:
            fnode = ["(assert " + to_smtlib(p.to_smt(symbol_table)[0], daggify=False) + ")" for p in props]
            fnode = "\n".join(fnode)
            print(fnode)
            # print(to_smtlib(fnode, daggify=False))
