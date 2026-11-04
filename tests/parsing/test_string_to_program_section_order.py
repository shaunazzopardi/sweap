from unittest import TestCase

from parsing.string_to_program import string_to_program
from prop_lang.update import Update
from prop_lang.biop import BiOp
from prop_lang.variable import Variable
from prop_lang.value import Value
from prop_lang.util import G, true


class TestStringToProgramSectionOrder(TestCase):
    def test_accepts_top_level_sections_in_noncanonical_order(self):
        program_text = """
        program reordered_sections_demo {
            STATES {
                q0 : init, q1
            }

            OUTPUTS {
                out : boolean
            }

            TRANSITIONS {
                q0 -> q1 [true # (x' = x + 1)],
                q1 -> q1 [true # (x' = x)]
            }

            VALUATION {
                x : integer := 0
            }

            INPUTS {
                request : boolean
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, spec = string_to_program(program_text)

        self.assertEqual({"q0", "q1"}, set(program.states))
        self.assertEqual(["request"], [str(v) for v, _ in program.env_events])
        self.assertEqual(["out"], [str(v) for v, _ in program.con_events])

        transition = next(t for t in program.orig_ts if t.src == "q0")
        self.assertEqual(transition.tgt, "q1")
        self.assertEqual(
            transition.action,
            [Update(Variable("x"), BiOp(Variable("x"), "+", Value(1)))],
        )
        self.assertEqual(spec, G(true()))
