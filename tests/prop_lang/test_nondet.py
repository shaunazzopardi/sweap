from unittest import TestCase

from prop_lang.nondet import NonDeterministic
from prop_lang.update import Update
from prop_lang.variable import Variable


class TestNonDeterministic(TestCase):
    def test_replace_formulas_noop(self):
        nd = NonDeterministic()
        self.assertIs(nd.replace_formulas({Variable("x"): Variable("y")}), nd)

    def test_update_replace_formulas_handles_nondet_rhs(self):
        u = Update(Variable("x"), NonDeterministic())
        replaced = u.replace_formulas({Variable("x"): Variable("z")})
        self.assertEqual(str(replaced.left), "z")
        self.assertEqual(str(replaced.right), "*")
