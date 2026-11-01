from contextlib import redirect_stdout
from io import StringIO
from unittest import TestCase

import config
from parsing.reserved_names import reserved_name_mapping, rename_formula
from parsing.string_to_issy import string_to_issy
from parsing.string_to_program import string_to_program
from parsing.string_to_rpg import rpg_parsec
from parsing.string_to_ltl import string_to_ltlmt
from parsing.string_to_ltlmt import ToProgram
from prop_lang.biop import BiOp
from prop_lang.variable import Variable
from synthesis.synthesis import process_specifications


class TestReservedNames(TestCase):
    def setUp(self):
        conf = config.Config.getConfig()
        old_workers = conf.workers
        conf.workers = 1
        self.addCleanup(setattr, conf, "workers", old_workers)
        self.output = redirect_stdout(StringIO())
        self.output.__enter__()
        self.addCleanup(self.output.__exit__, None, None, None)

    def test_prefix_repeats_without_merging_original_names(self):
        names = reserved_name_mapping({"i", "curr_i", "res_curr_i", "res_res_curr_i"})
        self.assertEqual(names, {"curr_i": "res_res_res_curr_i"})
        formula = BiOp(Variable("curr_i'"), "=", Variable("curr_i"))
        self.assertEqual(str(rename_formula(formula, names)),
                         "(res_res_res_curr_i' = res_res_res_curr_i)")

    def test_history_aliases_follow_their_renamed_state_variable(self):
        for name in ("curr_i_prev", "curr_i_prev'", "curr_i_prev_prev"):
            with self.subTest(name=name):
                renamed = rename_formula(Variable(name), {"curr_i": "res_curr_i"})
                self.assertEqual(str(renamed), "res_" + name)

    def test_prev_declarations_receive_a_collision_free_suffix(self):
        names = reserved_name_mapping(
            {"x", "x_prev", "x_prev_res", "x_prev_prev", "curr_i_prev"}
        )
        self.assertEqual(names["x_prev"], "x_prev_res_res")
        self.assertEqual(names["x_prev_prev"], "x_prev_prev_res")
        self.assertEqual(names["curr_i_prev"], "res_curr_i_prev_res")
        self.assertTrue(all(not name.endswith("_prev") for name in names.values()))
        self.assertEqual(
            str(rename_formula(Variable("x_prev'"), names)), "x_prev_res_res'"
        )

    def test_declared_prev_name_is_not_an_internal_lookback(self):
        program, objective = string_to_program("""
        program declared_prev {
          STATES { q: init }
          ENVIRONMENT EVENTS { }
          CONTROLLER EVENTS { }
          VALUATION { x: integer := 0; x_prev: integer := 1; }
          TRANSITIONS { q -> q [true $ x := x_prev; x_prev := x_prev + 1] }
          SPECIFICATION { G(x_prev >= 1) }
        }
        """)
        self.assertIn(Variable("x_prev_res"), program.local_vars)
        self.assertFalse(objective.has_prev_vars())
        self.assertIn(Variable("x_prev_res"), objective.variablesin())
        self.assertIn(Variable("x_prev_res"), program.transitions[0].action[0].variablesin())
        process_specifications(program, objective, None)

    def test_reserved_state_history_passes_ltl_validation_after_renaming(self):
        program, objective = string_to_program("""
        program reserved_history {
          STATES { q: init }
          ENVIRONMENT EVENTS { i: integer }
          CONTROLLER EVENTS { }
          VALUATION { curr_i: integer := 0; }
          TRANSITIONS { q -> q [true $ curr_i := i] }
          SPECIFICATION { X G(curr_i_prev = 0) }
        }
        """)
        self.assertIn(Variable("res_curr_i"), program.local_vars)
        self.assertIn(Variable("res_curr_i_prev"), objective.variablesin())
        self.assertNotIn(Variable("curr_i_prev"), objective.variablesin())
        process_specifications(program, objective, None)

    def test_issy_renames_macros_locations_and_all_variable_references(self):
        source = """
        input int i
        state int curr_i
        state int res_curr_i
        def pred_bound = [curr_i >= res_curr_i]
        formula { assert F pred_bound }
        game Safety from lose {
          loc lose 1
          from lose to lose with [curr_i' = i] && [res_curr_i' = curr_i]
        }
        """
        program, objective = string_to_issy(source, "reserved_res")
        text = program.to_issy(objective)
        self.assertIn("res_res_curr_i", text)
        self.assertIn("res_curr_i", text)
        self.assertIn("res_lose", text)
        self.assertNotIn("[curr_i", text)
        self.assertNotIn("pred_bound", text)

    def test_sweap_renames_reserved_state_and_valuation_names(self):
        source = """
        program reserved {
          STATES { lose: init }
          ENVIRONMENT EVENTS { i: integer }
          CONTROLLER EVENTS { }
          VALUATION { curr_i: integer; res_curr_i: integer; }
          TRANSITIONS { lose -> lose [true $ curr_i := i; res_curr_i := curr_i] }
          SPECIFICATION { F(curr_i > res_curr_i) }
        }
        """
        program, objective = string_to_program(source)
        text = program.to_prog(objective)
        self.assertIn("res_res_curr_i", text)
        self.assertIn("res_lose", text)
        self.assertNotIn("curr_i :=", text.replace("res_res_curr_i :=", "").replace("res_curr_i :=", ""))

    def test_rpg_renames_nested_update_destinations_and_conditions(self):
        source = """
        type Safety
        input i Int
        output curr_i Int
        loc lose 1
        init lose
        trans lose if (> curr_i 0) then sys (((curr_i i)) lose) else lose
        """
        program, objective = rpg_parsec(source.strip(), "reserved_res")
        text = program.to_prog(objective)
        self.assertIn("res_curr_i", text)
        self.assertIn("res_lose", text)
        self.assertNotIn(" curr_i ", text)

    def test_tsl_renames_inferred_and_declared_variables(self):
        parsed, _ = string_to_ltlmt(
            "guarantee { [curr_i <- i]; G (gt curr_i i0()); }"
        )
        program, objective = ToProgram().ltlmt2prog(
            parsed, var_decs={"curr_i": ("var", "Int"), "i": ("inp", "Int")}
        )
        self.assertIn("res_curr_i", program.symbol_table)
        self.assertNotIn("curr_i", program.symbol_table)
        self.assertIn("res_curr_i", str(objective))

    def test_duplicate_issy_declarations_still_fail(self):
        with self.assertRaisesRegex(Exception, "Duplicate Issy"):
            string_to_issy("state int curr_i\nstate int curr_i", "duplicate")

    def test_existing_reserved_patterns_are_renamed(self):
        reserved = {"init_state", "second_state", "compatible", "turn", "prog", "process", "cs", "pred_x", "bin_x", "mismatch",
                    "compatible_x", "guard_x", "act_x", "identity_x",
                    "counterstrategy_guard_x", "counterstrategy_act_x", "floor", "keep",
                    "eq_con_x", "sat_con_x", "con_0", "minigame_event_x", "env_lose", "lose"}
        names = reserved_name_mapping(reserved)
        self.assertEqual(set(names), reserved)
        self.assertEqual(set(names.values()), {"res_" + v for v in reserved})

    def test_boolean_literal_identifiers_are_rejected_in_every_format(self):
        for name in ("true", "false", "TRUE", "FALSE", "True", "False"):
            sources = {
                "sweap": lambda: string_to_program(f"""
                    program literal {{
                      STATES {{ q: init }}
                      ENVIRONMENT EVENTS {{ }}
                      CONTROLLER EVENTS {{ }}
                      VALUATION {{ {name}: integer; }}
                      TRANSITIONS {{ q -> q [TRUE $ {name} := 0] }}
                      SPECIFICATION {{ F(q) }}
                    }}
                """),
                "issy": lambda: string_to_issy(f"""
                    state int {name}
                    formula {{ assert F q }}
                    game Safety from q {{
                      loc q 1
                      from q to q with true
                    }}
                """, "literal_res"),
                "rpg": lambda: rpg_parsec(f"""type Safety
output {name} Int
loc q 1
init q
trans q q
""", "literal_res"),
                "tsl": lambda: string_to_ltlmt(
                    f"guarantee {{ [{name} <- i]; }}"
                ),
            }
            for kind, parse in sources.items():
                with self.subTest(name=name, format=kind):
                    with self.assertRaises(Exception):
                        parse()
            with self.subTest(name=name, format="shared mapping"):
                with self.assertRaisesRegex(ValueError, "Boolean literal"):
                    reserved_name_mapping({name})

    def test_commented_literal_declaration_does_not_rename_boolean_guards(self):
        program, _ = string_to_program("""
        program comments {
          STATES { q: init }
          ENVIRONMENT EVENTS { }
          CONTROLLER EVENTS { }
          VALUATION { x: integer := 0; }
          TRANSITIONS { q -> q [true $ x := x + 1] }
          SPECIFICATION { G(q) // true: integer
          }
        }
        """)
        self.assertTrue(program.transitions[0].condition.is_true())
        self.assertNotIn("res_true", program.symbol_table)
