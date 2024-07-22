from unittest import TestCase

from analysis.refinement.fairness_refinement.fairness_util import cones_of_influence_reduction
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.biop import BiOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_cones_of_influence_reduction(self):
        x = Variable("x")
        cnt = Variable("cnt")
        exit_cond = string_to_prop("cnt == 0")
        body = [[BiOp(cnt, ":=", BiOp(cnt, "-", Value("1")))]]
        body += [[BiOp(x, ":=", BiOp(cnt, "-", Value("1")))]]

        reduced, reduced_body, vars_relevant_to_exit = cones_of_influence_reduction(exit_cond, body)

        self.assertTrue(reduced and len(reduced_body) == 1 and len(vars_relevant_to_exit) == 1 and cnt in vars_relevant_to_exit)

    def test_cones_of_influence_reduction1(self):
        x = Variable("x")
        cnt = Variable("cnt")
        exit_cond = string_to_prop("cnt == 0 && x == 0")
        body = [[BiOp(cnt, ":=", BiOp(cnt, "-", Value("1")))]]
        body += [[BiOp(x, ":=", BiOp(cnt, "-", Value("1")))]]

        reduced, reduced_body, vars_relevant_to_exit = cones_of_influence_reduction(exit_cond, body)

        self.assertTrue(not reduced and len(reduced_body) == 2 and len(vars_relevant_to_exit) == 2 and cnt in vars_relevant_to_exit and x in vars_relevant_to_exit)
