from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

import config
from parsing.string_to_program import string_to_program
from programs.program import Program
from programs.util import symbol_table_from_program
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestInitialValuationValidation(TestCase):
    def test_initial_values_reject_every_kind_of_variable_reference(self):
        program = SimpleNamespace(
            states={"q"}, out_events=[],
            env_events=[(Variable("input_value"), INTEGER)],
            con_events=[(Variable("controller_event"), BOOLEAN)],
        )
        for name in (
            "x", "y", "q", "input_value", "controller_event", "unknown",
            "x_prev", "x_prev_prev", "input_value_prev", "x'",
        ):
            for expression in (
                Variable(name),
                BiOp(Variable(name), "+", Value("1")),
                BiOp(Variable(name), "-", Variable(name)),
            ):
                with self.subTest(expression=str(expression)):
                    with self.assertRaisesRegex(ValueError, "Initial value for 'x'.*variables"):
                        symbol_table_from_program(
                            program, [("x", INTEGER, expression), ("y", INTEGER)]
                        )

    def test_variable_free_expressions_and_unset_values_are_allowed(self):
        program = SimpleNamespace(states={"q"}, out_events=[], env_events=[], con_events=[])
        expressions = (
            ("x", INTEGER, Value("3")),
            ("sum", INTEGER, BiOp(Value("1"), "+", Value("2"))),
            ("flag", BOOLEAN, Value("TRUE")),
            ("choice", INTEGER, NonDeterministic()),
            ("unset", INTEGER),
        )
        _, initial, unset = symbol_table_from_program(program, expressions)
        self.assertEqual(set(initial), {"x", "sum", "flag", "choice"})
        self.assertEqual(unset, ["unset"])

    def test_direct_program_construction_rejects_before_preprocessing(self):
        with patch.object(Program, "refine_var_types") as refine:
            with self.assertRaisesRegex(ValueError, "Initial value for 'x'.*variables"):
                Program(
                    "invalid_initial", {"q"}, "q",
                    [("x", INTEGER, Variable("input_value"))], [],
                    [(Variable("input_value"), INTEGER)], [],
                    preprocess=False, is_determ=True,
                )
            refine.assert_not_called()

    def test_sweap_parser_uses_the_same_initial_value_validation(self):
        source = """
        program invalid_initial {
            STATES { q: init }
            ENVIRONMENT EVENTS { input_value: integer }
            CONTROLLER EVENTS { }
            VALUATION { x: integer := input_value; }
            TRANSITIONS { q -> q [true $ x := 0] }
            SPECIFICATION { G(x >= 0) }
        }
        """
        with patch.object(config.Config.getConfig(), "workers", 1):
            with self.assertRaisesRegex(ValueError, "Initial value for 'x'.*variables"):
                string_to_program(source)
