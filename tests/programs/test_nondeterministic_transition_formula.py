from unittest import TestCase

from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import INTEGER, NATURAL, parse_type
from prop_lang.update import Update
from prop_lang.util import conjunct, sat, true, type_constraints_acts
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestNondeterministicTransitionFormula(TestCase):
    def test_wildcard_leaves_next_value_free_and_preserves_other_updates(self):
        x, y = Variable('wild_x'), Variable('wild_y')
        transition = Transition(
            'q', true(), [Update(x, NonDeterministic()), Update(y, Value(3))], [], 'q'
        )
        relation = transition.formula()
        table = {x.name: INTEGER, y.name: INTEGER}
        for value in (-1, 0, 7):
            self.assertTrue(sat(conjunct(relation, BiOp(x, '=', Value(value))), table))
        self.assertFalse(sat(conjunct(relation, BiOp(y, '!=', Value(3))), table))

    def test_wildcard_has_no_source_guard_for_bounded_domains(self):
        x = Variable('wild_bounded')
        transition = Transition('q', true(), [Update(x, NonDeterministic())], [], 'q')
        for domain in (NATURAL, parse_type('[0..3]')):
            with self.subTest(domain=domain):
                self.assertEqual(type_constraints_acts(transition, {x.name: domain}), [])
