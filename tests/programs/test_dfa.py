from unittest import TestCase

from parsing.string_to_program import string_to_program
from programs.dfa import program_sccs


class Test(TestCase):
    def test_only_init_transitions_when_initial_state_is_not_reachable_again(self):
        program_text = """
        program init_once_demo {
            STATES {
                q0 : init, q1
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
                q1 -> q1 [true]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)

        self.assertEqual(1, len(program.only_init_transitions))
        self.assertEqual("q0", program.only_init_transitions[0].src)
        self.assertEqual("q1", program.only_init_transitions[0].tgt)

    def test_only_init_transitions_when_init_state_reachable_in_rest_of_program(self):
        program_text = """
        program init_branch_filter_demo {
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
                q0 -> q0 [true],
                q0 -> q1 [true],
                q1 -> q2 [true],
                q2 -> q2 [true]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)

        self.assertEqual(0, len(program.only_init_transitions))
        self.assertEqual("q0", program.only_init_transitions[0].src)
        self.assertEqual("q1", program.only_init_transitions[0].tgt)

    def test_only_init_transitions_empty_when_all_init_branches_can_return(self):
        program_text = """
        program init_all_return_demo {
            STATES {
                q0 : init, q1
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0;
            }

            TRANSITIONS {
                q0 -> q0 [true],
                q0 -> q1 [true],
                q1 -> q0 [true]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)

        self.assertEqual([], program.only_init_transitions)

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
