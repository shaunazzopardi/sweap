from unittest import TestCase

from prop_lang.util import dnf, conjunct, disjunct, neg, false
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_dnf(self):
        input = conjunct(Variable("p"), Variable("q"))
        res = dnf(input)
        self.assertTrue(res == input)

    def test_dnf_0(self):
        input = disjunct(Variable("p"), Variable("q"))
        res = dnf(conjunct(input, input))
        self.assertTrue(res == input)

    def test_dnf_1(self):
        input = disjunct(Variable("p"), Variable("q"))
        res = dnf(conjunct(input, neg(input)))
        self.assertTrue(isinstance(res, Value) and res.is_false())
