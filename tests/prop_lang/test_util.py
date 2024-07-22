from unittest import TestCase

from parsing.string_to_prop_logic import string_to_prop
from prop_lang.util import dnf, conjunct, disjunct, neg, cnf
from prop_lang.value import Value
from prop_lang.variable import Variable
import time

class Test(TestCase):
    def test_dnf(self):
        input = conjunct(Variable("p"), Variable("q"))
        res = dnf(input)
        self.assertTrue(res == input)

    def test_dnf_0(self):
        input = disjunct(Variable("p"), Variable("q"))
        res = dnf(conjunct(input, input))
        self.assertTrue(len(str(res)) == len(str(input)))

    def test_dnf_1(self):
        input = disjunct(Variable("p"), Variable("q"))
        res = dnf(conjunct(input, neg(input)))
        self.assertTrue(isinstance(res, Value) and res.is_false())

    def test_string_to_prop(self):
        example = "(((0 & (2 | 3 | 4 | 7 | 8 | 11 | 13 | 15 | 17 | !18 | !10 | !9 | !6 | !5)) | (!0 & ((1 & ((2 & (4 | 5 | 7 | 8 | 10 | 13 | 16 | 18 | !17 | !11 | !9 | !3)) | (!2 & ((3 & ((4 & ((5 & (7 | 8 | 13 | 17 | 18 | !16 | !11 | !10 | !9 | !6)) | (!5 & (7 | 8 | 10 | 13 | 17 | 18 | !16 | !11 | !9)))) | (!4 & ((5 & ((7 & (8 | 13 | 17 | 18 | !15 | !11 | !10 | !9)) | (!7 & (8 | 13 | (15 & ((16 & 17 & 18) | (!16 & 17))) | (!15 & ((16 & 18) | (!16 & (17 | 18)))) | !11 | !10 | !9)) | !6)) | (!5 & (7 | 8 | 10 | 13 | (16 & (18 | !17)) | (!16 & (17 | 18)) | !11 | !9)))))) | (!3 & (4 | (7 & (8 | 11 | 13 | 17 | 18 | !15 | !10 | !9)) | (!7 & (8 | 11 | 13 | (15 & (17 | !18)) | (!15 & (17 | 18)) | !10 | !9)) | !6 | !5)))))) | (!1 & (2 | 3 | 4 | (7 & (8 | 11 | 13 | 17 | 18 | !15 | !10 | !9)) | (!7 & (8 | 11 | 13 | (15 & (17 | !18)) | (!15 & (17 | 18)) | !10 | !9)) | !6 | !5))))) & true)"

        start = time.time()
        example = example.replace("0", "a")
        example = example.replace("1", "b")
        example = example.replace("2", "c")
        example = example.replace("3", "d")
        example = example.replace("4", "e")
        example = example.replace("5", "f")
        example = example.replace("6", "g")
        example = example.replace("7", "h")
        example = example.replace("8", "i")
        example = example.replace("9", "j")

        formula = string_to_prop(example)
        print(formula)
        end = time.time()
        print(end - start)

        example_alpha = "(((pred__crprev_LT_cr_1 & (pred__crprev_LT_cr_ | pred__cl_LT__EQ_0_ | pred__crprev_GT_cr_ | pred__clprev_GT_cl_ | q1 | empty_l | danger | exit_r | entry_r | !entry_l | !empty_r | !q0 | !pred__cr_LT__EQ_1_ | !pred__cr_LT__EQ_0_)) | (!pred__crprev_LT_cr_1 & ((pred__clprev_LT_cl_ & ((pred__crprev_LT_cr_ & (pred__crprev_GT_cr_ | pred__cr_LT__EQ_0_ | pred__clprev_GT_cl_ | q1 | empty_r | danger | exit_l | entry_l | !entry_r | !empty_l | !q0 | !pred__cl_LT__EQ_0_)) | (!pred__crprev_LT_cr_ & ((pred__cl_LT__EQ_0_ & ((pred__crprev_GT_cr_ & ((pred__cr_LT__EQ_0_ & (pred__clprev_GT_cl_ | q1 | danger | entry_r | entry_l | !exit_l | !empty_l | !empty_r | !q0 | !pred__cr_LT__EQ_1_)) | (!pred__cr_LT__EQ_0_ & (pred__clprev_GT_cl_ | q1 | empty_r | danger | entry_r | entry_l | !exit_l | !empty_l | !q0)))) | (!pred__crprev_GT_cr_ & ((pred__cr_LT__EQ_0_ & ((pred__clprev_GT_cl_ & (q1 | danger | entry_r | entry_l | !exit_r | !empty_l | !empty_r | !q0)) | (!pred__clprev_GT_cl_ & (q1 | danger | (exit_r & ((exit_l & entry_r & entry_l) | (!exit_l & entry_r))) | (!exit_r & ((exit_l & entry_l) | (!exit_l & (entry_r | entry_l)))) | !empty_l | !empty_r | !q0)) | !pred__cr_LT__EQ_1_)) | (!pred__cr_LT__EQ_0_ & (pred__clprev_GT_cl_ | q1 | empty_r | danger | (exit_l & (entry_l | !entry_r)) | (!exit_l & (entry_r | entry_l)) | !empty_l | !q0)))))) | (!pred__cl_LT__EQ_0_ & (pred__crprev_GT_cr_ | (pred__clprev_GT_cl_ & (q1 | empty_l | danger | entry_r | entry_l | !exit_r | !empty_r | !q0)) | (!pred__clprev_GT_cl_ & (q1 | empty_l | danger | (exit_r & (entry_r | !entry_l)) | (!exit_r & (entry_r | entry_l)) | !empty_r | !q0)) | !pred__cr_LT__EQ_1_ | !pred__cr_LT__EQ_0_)))))) | (!pred__clprev_LT_cl_ & (pred__crprev_LT_cr_ | pred__cl_LT__EQ_0_ | pred__crprev_GT_cr_ | (pred__clprev_GT_cl_ & (q1 | empty_l | danger | entry_r | entry_l | !exit_r | !empty_r | !q0)) | (!pred__clprev_GT_cl_ & (q1 | empty_l | danger | (exit_r & (entry_r | !entry_l)) | (!exit_r & (entry_r | entry_l)) | !empty_r | !q0)) | !pred__cr_LT__EQ_1_ | !pred__cr_LT__EQ_0_))))) & true)"

        start = time.time()
        formula2 = string_to_prop(example_alpha, hoa_flag=True)
        print(formula2)
        end = time.time()
        print(end - start)

        self.assertTrue(True)

    def test_to_cnf(self):
        formula1 = "(!empty_l & !danger & !entry_r & entry_l & exit_r & l2r & empty_r)"
        formula1 = string_to_prop(formula1)
        formula2 = "(!empty_l & !danger & !exit_r & !entry_r & !entry_l & l2r & empty_r)"
        formula2 = string_to_prop(formula2)

        formula = cnf(disjunct(formula1, formula2))
        print(str(formula))


