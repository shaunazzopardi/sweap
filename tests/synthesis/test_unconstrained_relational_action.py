from unittest import TestCase

from parsing.string_to_program import string_to_program
from prop_lang.nondet import NonDeterministic
from synthesis.synthesis import synthesize


class TestUnconstrainedRelationalAction(TestCase):
    def test_unconstrained_choices_reach_goal(self):
        for name, domain, initial, goal in (
            ('choice_int', 'integer', '0', 'F(choice_int = 1)'),
            ('choice_bool', 'boolean', 'false', 'F(choice_bool)'),
            ('choice_bounded', '[0..2]', '0', 'F(choice_bounded = 2)'),
        ):
            with self.subTest(domain=domain):
                program, spec = string_to_program(f"""
                    program unconstrained_choice {{
                        STATES {{ q : init }}
                        ENVIRONMENT EVENTS {{}}
                        CONTROLLER EVENTS {{}}
                        VALUATION {{ {name} : {domain} := {initial}; }}
                        TRANSITIONS [completion=stutter] {{ q -> q [true #] }}
                        SPECIFICATION {{ {goal} }}
                    }}
                """)
                self.assertFalse(any(
                    isinstance(update.right, NonDeterministic)
                    for transition in program.transitions
                    for update in transition.action
                ))
                self.assertTrue(synthesize(program, spec, None).realisable)
