from unittest import TestCase

from parsing.string_to_program import string_to_program
from programs.dfa import program_sccs


class Test(TestCase):
    def test_program_sccs_transitions(self):
        program_text = """
        program scc_demo {
            STATES {
                q0 : init, q1, q2
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0;
            }

            TRANSITIONS {
                q0 -> q1 [true],
                q1 -> q2 [true],
                q2 -> q1 [true],
                q2 -> q2 [true]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        sccs = program_sccs(program)

        q12_transitions = {
            t
            for t in program.transitions
            if t.src in {"q1", "q2"} and t.tgt in {"q1", "q2"}
        }
        self.assertTrue(any(scc == q12_transitions for scc in sccs))

        q0_transitions = {
            t for t in program.transitions if t.src == "q0" and t.tgt == "q0"
        }
        self.assertTrue(any(scc == q0_transitions for scc in sccs))

    def test_program_sccs_multiple_components(self):
        program_text = """
        program scc_demo_2 {
            STATES {
                q0 : init, q1, q2, q3
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0;
            }

            TRANSITIONS {
                q0 -> q1 [true],
                q1 -> q2 [true],
                q2 -> q1 [true],
                q2 -> q3 [true],
                q3 -> q3 [true]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        sccs = program_sccs(program)

        q12_transitions = {
            t
            for t in program.transitions
            if t.src in {"q1", "q2"} and t.tgt in {"q1", "q2"}
        }
        q3_transitions = {
            t for t in program.transitions if t.src == "q3" and t.tgt == "q3"
        }
        q0_transitions = {
            t for t in program.transitions if t.src == "q0" and t.tgt == "q0"
        }
        q2_to_q3 = {t for t in program.transitions if t.src == "q2" and t.tgt == "q3"}

        self.assertTrue(any(scc == q12_transitions for scc in sccs))
        self.assertTrue(any(scc == q3_transitions for scc in sccs))
        self.assertTrue(any(scc == q0_transitions for scc in sccs))
        self.assertTrue(all(t not in scc for scc in sccs for t in q2_to_q3))
