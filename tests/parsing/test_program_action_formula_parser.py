from unittest import TestCase

from parsing.string_to_program import (
    make_program_action_formula_parser,
    make_transition_special_action_parser,
    parse_program_action_formula_text,
    string_to_program,
)
from prop_lang.formula import Formula


class TestProgramActionFormulaParser(TestCase):
    def test_parses_boolean_combo_over_now_and_next_program_vars(self):
        result = parse_program_action_formula_text(
            "(x' = x + 1) & (y' = y - 1)", {"x", "y"}
        )

        self.assertIsInstance(result, Formula)
        self.assertIn("&", str(result))
        self.assertEqual(
            {str(v) for v in result.variablesin()},
            {"x", "x'", "y", "y'"},
        )

    def test_rejects_unknown_variables(self):
        with self.assertRaises(Exception) as ctx:
            parse_program_action_formula_text("(x' = x + 1) & req", {"x"})

        self.assertIn("local state variables", str(ctx.exception))
        self.assertIn("req", str(ctx.exception))

    def test_allows_now_input_output_variables(self):
        result = parse_program_action_formula_text(
            "(x' = x + 1) & req & !grant",
            {"x"},
            {"req", "grant"},
        )

        self.assertIsInstance(result, Formula)
        self.assertEqual(
            {str(v) for v in result.variablesin()},
            {"x", "x'", "req", "grant"},
        )

    def test_rejects_nexted_input_output_variables(self):
        with self.assertRaises(Exception) as ctx:
            parse_program_action_formula_text(
                "(x' = x + 1) & req'",
                {"x"},
                {"req"},
            )

        self.assertIn("now only", str(ctx.exception))
        self.assertIn("req'", str(ctx.exception))

    def test_rejects_ltl_operators(self):
        with self.assertRaises(Exception):
            parse_program_action_formula_text("X(x' = x + 1)", {"x"})

    def test_parsec_parser_factory_uses_same_validation(self):
        parser = make_program_action_formula_parser({"x", "y"})
        result = (parser << __import__("parsec").eof()).parse("(x' = y) | (y' = x)")

        self.assertIsInstance(result, Formula)
        self.assertIn("|", str(result))
        self.assertEqual(
            {str(v) for v in result.variablesin()},
            {"x", "y", "x'", "y'"},
        )

    def test_transition_action_formula_parser_captures_after_hash(self):
        parsec = __import__("parsec")
        parser = make_transition_special_action_parser({"x", "y"})
        result = (parser << parsec.string("]") << parsec.eof()).parse(
            "# (x' = x + 1) & (y' = x) ]"
        )

        self.assertIsInstance(result, Formula)
        self.assertIn("&", str(result))
        self.assertEqual(
            {str(v) for v in result.variablesin()},
            {"x", "x'", "y'"},
        )

    def test_transition_action_formula_parser_treats_empty_hash_as_true(self):
        parsec = __import__("parsec")
        parser = make_transition_special_action_parser({"x", "y"})
        result = (parser << parsec.string("]") << parsec.eof()).parse("# ]")

        self.assertIsInstance(result, Formula)
        self.assertEqual(str(result), "TRUE")

    def test_string_to_program_lowers_relational_action_with_issy_path(self):
        program_text = """
        program relational_action_demo {
            STATES {
                q0 : init, q1
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0;
                y : integer := 0;
            }

            TRANSITIONS [completion=stutter] {
                q0 -> q1 [true # (x' = x + 1) & (y' = x)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        relevant = [t for t in program.orig_ts if t.src == "q0" and t.tgt == "q1"]

        self.assertEqual(len(relevant), 1)
        updates = {str(a.left): str(a.right) for a in relevant[0].action}
        self.assertEqual(updates["x"], "(x + 1)")
        self.assertEqual(updates["y"], "x")
        self.assertEqual(relevant[0].pred_upgrades, [])
        self.assertEqual(str(program.init_var_values["x"]), "0")
        self.assertEqual(str(program.init_var_values["y"]), "0")

    def test_string_to_program_determinises_branching_relational_action(self):
        program_text = """
        program branching_relational_action_demo {
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

            TRANSITIONS [completion=stutter] {
                q0 -> q1 [true # (x' = 0) | (x' = 1)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)

        self.assertTrue(program.deterministic)
        self.assertTrue(
            any(
                ev.name.startswith("sat_con_cp_") or ev.name.startswith("eq_con_cp_")
                for ev, _ in program.con_events
            )
        )
        relevant = [t for t in program.orig_ts if t.src == "q0" and t.tgt == "q1"]
        self.assertEqual(len(relevant), 2)
        self.assertEqual(
            {str(a.right) for t in relevant for a in t.action if str(a.left) == "x"},
            {"0", "1"},
        )

    def test_string_to_program_resolves_otherwise_before_branching_special_action(self):
        program_text = """
        program otherwise_branching_relational_action_demo {
            STATES {
                q0 : init, q1
            }

            ENVIRONMENT EVENTS {
                i : boolean
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer := 0;
            }

            TRANSITIONS [completion=stutter] {
                q0 -> q1 [i # (x' = x)],
                q0 -> q1 [otherwise # (x' = 0) | (x' = 1)],
                q1 -> q1 [true # (x' = x)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        q0_to_q1 = [t for t in program.orig_ts if t.src == "q0" and t.tgt == "q1"]

        self.assertTrue(len(q0_to_q1) >= 2)
        self.assertFalse(any(str(t.condition) == "otherwise" for t in q0_to_q1))

    def test_string_to_program_generates_minigame_for_relational_pred_upgrades(self):
        program_text = """
        program buggy_style_relational_action_demo {
            STATES {
                l1 : init, l0
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer;
            }

            TRANSITIONS {
                l1 -> l1 [true # (x' < 0) & (x' > x)],
                l1 -> l0 [true],
                l0 -> l0 [true]
            }

            SPECIFICATION {
                G(l1)
            }
        }
        """

        program, spec = string_to_program(program_text)

        self.assertTrue(any("minigame" in s for s in program.states))
        self.assertIn("int_x", program.symbol_table)
        self.assertTrue(any(t.tgt == "l1_minigame_0" for t in program.orig_ts))
        self.assertIn("G(F(!l1_minigame_0))", str(spec))

    def test_string_to_program_reuses_equivalent_minigames(self):
        program_text = """
        program buggy2_style_relational_action_demo {
            STATES {
                l1 : init, l0
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer;
            }

            TRANSITIONS {
                l1 -> l1 [x > 0 # (x != 2 & ((x' - x) > 1)) | (x == 2 & ((x' - x) > 0))],
                l1 -> l0 [x <= 0],
                l0 -> l0 [true]
            }

            SPECIFICATION {
                G(l1)
            }
        }
        """

        program, spec = string_to_program(program_text)

        minigame_states = sorted(s for s in program.states if "minigame" in s)
        self.assertEqual(minigame_states, ["l1_minigame_0"])
        self.assertEqual(
            sorted(
                t.tgt
                for t in program.orig_ts
                if t.src == "l1" and "x > 0" in str(t.condition)
            ),
            ["l1_minigame_0", "l1_minigame_0"],
        )
        self.assertIn("G(F(!l1_minigame_0))", str(spec))

    def test_reused_minigame_keeps_branch_specific_entry_update(self):
        program_text = """
        program reused_minigame_entry_update_demo {
            STATES {
                l1 : init, l0
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer;
            }

            TRANSITIONS {
                l1 -> l1 [x > 0 & x != 2 # ((x' - x) > 1)],
                l1 -> l1 [x > 0 & x == 2 # ((x' - x) > 0)],
                l1 -> l0 [x <= 0],
                l0 -> l0 [true]
            }

            SPECIFICATION {
                G(l1)
            }
        }
        """

        program, spec = string_to_program(program_text)

        minigame_states = sorted(s for s in program.states if "minigame" in s)
        self.assertEqual(minigame_states, ["l1_minigame_0"])

        branch_to_minigame = [
            t for t in program.orig_ts if t.src == "l1" and t.tgt == "l1_minigame_0"
        ]
        self.assertEqual(len(branch_to_minigame), 2)

        x_eq_2_transition = next(
            t for t in branch_to_minigame if "x = 2" in str(t.condition)
        )
        updates = {str(a.left): str(a.right) for a in x_eq_2_transition.action}

        self.assertEqual(updates["x"], "(x + 1)")
        self.assertIn("G(F(!l1_minigame_0))", str(spec))

    def test_string_to_program_empty_special_action_allows_any_next_state(self):
        program_text = """
        program empty_relational_action_demo {
            STATES {
                q0 : init, q1
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : natural := 0;
                y : natural := 1;
            }

            TRANSITIONS [completion=stutter] {
                q0 -> q1 [true #]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, _ = string_to_program(program_text)
        relevant = [t for t in program.orig_ts if t.src == "q0" and t.tgt == "q1"]

        self.assertEqual(len(relevant), 1)
        # Both choices are irrelevant to G true and may be replaced by stuttering.
        self.assertTrue(all(str(u.right) != "*" for t in program.transitions for u in t.action))
        self.assertEqual(relevant[0].pred_upgrades, [])

    def test_string_to_program_adds_lose_transition_for_uncovered_special_action_region(
        self,
    ):
        program_text = """
        program partial_relational_action_demo {
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

            TRANSITIONS [completion=lose] {
                q0 -> q1 [x > 0 # x == 1 & (x' = x + 1)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, spec = string_to_program(program_text)

        self.assertIn("lose", program.states)
        self.assertTrue(
            any(
                t.src == "q0" and t.tgt == "q1" and "x = 1" in str(t.condition)
                for t in program.orig_ts
            )
        )
        self.assertTrue(
            any(
                t.src == "q0" and t.tgt == "lose"
                for t in program.orig_ts
            )
        )
        self.assertIn("G(!lose)", str(spec))

    def test_string_to_program_adds_lose_transition_when_special_action_is_unsat(self):
        program_text = """
        program unsat_relational_action_demo {
            STATES {
                l1 : init, l0
            }

            ENVIRONMENT EVENTS {
            }

            CONTROLLER EVENTS {
            }

            VALUATION {
                x : integer;
            }

            TRANSITIONS [completion=lose] {
                l1 -> l1 [x > 0 # x == 1 & (x' < 0) & ((x' - x) > 0)],
                l1 -> l0 [x <= 0],
                l0 -> l0 [true]
            }

            SPECIFICATION {
                G(l1)
            }
        }
        """

        program, spec = string_to_program(program_text)

        self.assertIn("lose", program.states)
        self.assertTrue(
            any(
                t.src == "l1" and t.tgt == "lose"
                for t in program.orig_ts
            )
        )
        self.assertFalse(any(t.src == "l1" and t.tgt == "l1" for t in program.orig_ts))
        self.assertIn("G(!lose)", str(spec))

    def test_string_to_program_adds_stutter_transition_for_uncovered_special_action_region(
        self,
    ):
        program_text = """
        program partial_relational_action_stutter_demo {
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

            TRANSITIONS [completion=stutter] {
                q0 -> q1 [x > 0 # x == 1 & (x' = x + 1)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        program, spec = string_to_program(program_text)

        self.assertNotIn("lose", program.states)
        self.assertTrue(
            any(
                t.src == "q0" and t.tgt == "q1" and "x = 1" in str(t.condition)
                for t in program.orig_ts
            )
        )
        self.assertTrue(
            any(
                t.src == "q0" and t.tgt == "q0"
                for t in program.stutter_ts
            )
        )
        self.assertNotIn("G(!lose)", str(spec))

    def test_string_to_program_rejects_incomplete_special_action_without_completion(
        self,
    ):
        program_text = """
        program partial_relational_action_no_completion_demo {
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
                q0 -> q1 [x > 0 # x == 1 & (x' = x + 1)]
            }

            SPECIFICATION {
                G true
            }
        }
        """

        with self.assertRaises(Exception) as ctx:
            string_to_program(program_text)

        self.assertIn("Incomplete transitions from state(s): q0", str(ctx.exception))
