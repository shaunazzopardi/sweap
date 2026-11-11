from unittest import TestCase

from parsing.string_to_program import string_to_program
from prop_lang.util import equivalent, neg
from prop_lang.variable import Variable
from prop_lang.types.types import BOOLEAN
from prop_lang.update import Update
from prop_lang.biop import BiOp
from prop_lang.value import Value


class TestOtherwiseFallbackStutter(TestCase):
    def test_otherwise_transition_replaces_implicit_stutter_from_source_state(self):
        program_text = """
        program otherwise_fallback_demo {
            STATES {
                con : init, env
            }

            ENVIRONMENT EVENTS {
                i : boolean
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0
            }

            TRANSITIONS [completion=stutter] {
                con -> env [i $ x := x + 1],
                con -> env [otherwise $ x := x]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        from_con = [t for t in program.transitions if t.src == "con"]

        self.assertEqual(2, len(from_con))
        self.assertTrue(all(t.tgt == "env" for t in from_con))
        self.assertFalse(any(t.tgt == "con" for t in from_con))
        self.assertFalse(any(str(t.condition) == "otherwise" for t in from_con))
        self.assertFalse(any(t.src == "con" for t in program.stutter_ts))
        i, x = Variable("i"), Variable("x")
        fallback = [
            t for t in from_con if equivalent(t.condition, neg(i), {"i": BOOLEAN})
        ]
        ordinary = [t for t in from_con if equivalent(t.condition, i, {"i": BOOLEAN})]
        self.assertEqual(len(fallback), 1)
        self.assertEqual(len(ordinary), 1)
        self.assertEqual(fallback[0].action, [Update(x, x)])
        self.assertEqual(ordinary[0].action, [Update(x, BiOp(x, "+", Value(1)))])

    def test_otherwise_is_allowed_once_per_source_state(self):
        program_text = """
        program otherwise_per_source_demo {
            STATES {
                s0 : init, s1, s2
            }

            ENVIRONMENT EVENTS {
                i : boolean
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0
            }

            TRANSITIONS [completion=stutter] {
                s0 -> s1 [otherwise $ x := x],
                s1 -> s2 [otherwise $ x := x]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        self.assertEqual(2, len([t for t in program.orig_ts if t.tgt in {"s1", "s2"}]))

    def test_duplicate_otherwise_from_same_source_is_rejected(self):
        text = """
        program duplicate_otherwise {
            STATES { s0 : init, s1 }
            ENVIRONMENT EVENTS { i : boolean }
            CONTROLLER EVENTS { }
            VALUATION { x : integer := 0 }
            TRANSITIONS [completion=stutter] {
                s0 -> s0 [otherwise $ x := x],
                s0 -> s1 [otherwise $ x := x]
            }
            SPECIFICATION { G true }
        }
        """
        with self.assertRaisesRegex(Exception, "Too many 'otherwise'.*s0"):
            string_to_program(text)
