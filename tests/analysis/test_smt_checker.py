from unittest import TestCase

import pysmt
from pysmt.shortcuts import (
    And,
    Solver,
    serialize,
    to_smtlib,
    Symbol,
    Exists,
    ForAll,
    Implies,
)
from pysmt.typing import INT
from sympy.core import symbol

from analysis.smt_checker import (
    sequence_interpolant,
    binary_interpolant,
    quantifier_elimination,
    choose_model,
)
from parsing import string_to_ltl
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.util import (
    is_tautology,
    neg,
    conjunct,
    fnode_to_formula,
    formula_with_next_to_without,
    iff,
    unsat_core,
    sat,
)
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
            "e_0": INTEGER,
            "e_1": INTEGER,
            "c_0": INTEGER,
            "c_1": INTEGER,
            "set_e": INTEGER,
        }

        exist_vars = [Symbol("e_0", INT), Symbol("c_0", INT), Symbol("set_e", INT)]
        forall_vars = [Symbol("c_1", INT), Symbol("e_1", INT)]
        quant_formula = Exists(
            exist_vars,
            ForAll(
                forall_vars,
                Implies(p0.to_smt(symbol_table)[0], p1.to_smt(symbol_table)[0]),
            ),
        )

        ret = quantifier_elimination(quant_formula)
        rett = fnode_to_formula(ret)
        print()

    def test_remove(self):
        one = "		((!con_act_0 && !con_act_1 && (((bin_i_x0 && X(bin_i_x0)) || (!bin_i_x0 && bin_i_x1 && X(bin_i_x0)) || (!bin_i_x0 && !bin_i_x1 && (X((!bin_i_x0 && bin_i_x1)) || X((!bin_i_x0 && !bin_i_x1))))) && (bin_loc0 <-> X(bin_loc0)) && (bin_i_y0 <-> X(bin_i_y0)) && (bin_i_y1 <-> X(bin_i_y1)) && (bin_loc1 <-> X(bin_loc1)) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_)) && X((pred__ix_LT_ixprev_ && !pred__ixprev_LT_ix_))) && X((!bin_st_0 && bin_st_1))) || (!con_act_0 && con_act_1 && (((bin_i_x0 && (X(bin_i_x0) || X((!bin_i_x0 && bin_i_x1)))) || (!bin_i_x0 && bin_i_x1 && X((!bin_i_x0 && !bin_i_x1))) || (!bin_i_x0 && !bin_i_x1 && X((!bin_i_x0 && !bin_i_x1)))) && (bin_loc0 <-> X(bin_loc0)) && (bin_i_y0 <-> X(bin_i_y0)) && (bin_i_y1 <-> X(bin_i_y1)) && (bin_loc1 <-> X(bin_loc1)) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_)) && X((pred__ixprev_LT_ix_ && !pred__ix_LT_ixprev_))) && X((!bin_st_0 && bin_st_1))) || (con_act_0 && ((bin_i_x1 <-> X(bin_i_x1)) && (bin_i_y1 <-> X(bin_i_y1)) && (bin_loc0 <-> X(bin_loc0)) && (bin_i_x0 <-> X(bin_i_x0)) && (bin_i_y0 <-> X(bin_i_y0)) && (bin_loc1 <-> X(bin_loc1)) && X((!pred__ix_LT_ixprev_ && !pred__ixprev_LT_ix_))) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_)) && X((!bin_st_0 && bin_st_1))))"
        two = "		((!con_act_0 && !con_act_1 && (((bin_i_x0 && X(bin_i_x0)) || (!bin_i_x0 && bin_i_x1 && X(bin_i_x0)) || (!bin_i_x0 && !bin_i_x1 && (X((!bin_i_x0 && bin_i_x1)) || X((!bin_i_x0 && !bin_i_x1))))) && (bin_loc0 <-> X(bin_loc0) && (bin_i_y0 <-> X(bin_i_y0))) && (bin_i_y1 <-> X(bin_i_y1)) && (bin_loc1 <-> X(bin_loc1)) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_)) && X((pred__ix_LT_ixprev_ && !pred__ixprev_LT_ix_))) && X((!bin_st_0 && bin_st_1))) || (con_act_0 && ((bin_i_x0 <-> X(bin_i_x0)) && (bin_loc0 <-> X(bin_loc0)) && (bin_i_x1 <-> X(bin_i_x1)) && (bin_i_y0 <-> X(bin_i_y0)) && (bin_loc1 <-> X(bin_loc1)) && (bin_i_y1 <-> X(bin_i_y1)) && X((!pred__ix_LT_ixprev_ && !pred__ixprev_LT_ix_)) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_))) && X((!bin_st_0 && bin_st_1))) || (!con_act_0 && con_act_1 && (((bin_i_x0 && (X(bin_i_x0) || X((!bin_i_x0 && bin_i_x1)))) || (!bin_i_x0 && bin_i_x1 && X((!bin_i_x0 && !bin_i_x1))) || (!bin_i_x0 && !bin_i_x1 && X((!bin_i_x0 && !bin_i_x1)))) && (bin_i_y0 <-> X(bin_i_y0)) && (bin_loc0 <-> X(bin_loc0)) && (bin_loc1 <-> X(bin_loc1)) && (bin_i_y1 <-> X(bin_i_y1)) && X((pred__ixprev_LT_ix_ && !pred__ix_LT_ixprev_)) && X((!pred__iy_LT_iyprev_ && !pred__iyprev_LT_iy_))) && X((!bin_st_0 && bin_st_1))))"

        one = "((bin_i_x0 && !bin_loc0 && bin_loc1 && bin_i_y0) || (!bin_i_x0 && bin_i_x1 && !bin_loc0 && bin_loc1 && bin_i_y0) || (!bin_i_x0 && !bin_i_x1 && !bin_loc0 && bin_loc1 && bin_i_y0) || (bin_i_x0 && !bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1) || (!bin_i_x0 && bin_i_x1 && !bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1) || (!bin_i_x0 && !bin_i_x1 && !bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1) || (bin_i_x0 && !bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1) || (!bin_i_x0 && bin_i_x1 && !bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1) || (!bin_i_x0 && !bin_i_x1 && !bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1))"

        two = "((!bin_loc0 && bin_loc1 && bin_i_y0 && bin_i_x0) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1 && bin_i_x0) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1 && bin_i_x0) || (!bin_loc0 && bin_loc1 && bin_i_y0 && !bin_i_x0 && bin_i_x1) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1 && !bin_i_x0 && bin_i_x1) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1 && !bin_i_x0 && bin_i_x1) || (!bin_loc0 && bin_loc1 && bin_i_y0 && !bin_i_x0 && !bin_i_x1) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && bin_i_y1 && !bin_i_x0 && !bin_i_x1) || (!bin_loc0 && bin_loc1 && !bin_i_y0 && !bin_i_y1 && !bin_i_x0 && !bin_i_x1))"

        one = one.replace("bin_", "b_").replace("pred_", "p_")
        two = two.replace("bin_", "b_").replace("pred_", "p_")
        # one = "((((((b_i_x0 & b_i_x0_next) | (((! b_i_x0) & b_i_x1) & b_i_x0_next)) | (((! b_i_x0) & (! b_i_x1)) & (((! b_i_x0_next) & b_i_x1_next) | ((! b_i_x0_next) & (! b_i_x1_next))))))))"
        # two = "((((((b_i_x0 & b_i_x0_next) | (((! b_i_x0) & b_i_x1) & b_i_x0_next)) | (((! b_i_x0) & (! b_i_x1)) & (((! b_i_x0_next) & b_i_x1_next) | ((! b_i_x0_next) & (! b_i_x1_next))))))))"
        f1 = string_to_ltl.string_to_ltl_with_predicates(one)
        f2 = string_to_ltl.string_to_ltl_with_predicates(two)

        f1 = formula_with_next_to_without(f1)
        f2 = formula_with_next_to_without(f2)
        symbol_table = {str(v): BOOLEAN for v in conjunct(f1, f2).variablesin()}
        core = unsat_core(iff(f1, f2), symbol_table)
        if core:
            for s in unsat_core(iff(f1, f2), symbol_table):
                print(str(s))

        if sat(neg(iff(f1, f2)), symbol_table):
            model = choose_model(neg(iff(f1, f2)).to_smt(symbol_table)[0])
            print(str(model))

            print(serialize(f1.left.to_smt(symbol_table)[0]))
            print(serialize(f2.left.to_smt(symbol_table)[0]))
