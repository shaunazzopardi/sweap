from unittest import TestCase
from unittest.mock import patch

import config
from parsing.string_to_ltl import string_to_ltl_with_predicates
from parsing.string_to_program import string_to_program
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.synthesis import process_specifications


class TestHistoryReferenceValidation(TestCase):
    @staticmethod
    def _program(condition=None, action=None, pred_upgrade=None, constant_flag=False):
        transition = Transition(
            "run", condition if condition is not None else true(),
            action if action is not None else [
                Update(Variable("x"), BiOp(Variable("x"), "+", Value("1")))
            ], [], "run",
        )
        if pred_upgrade is not None:
            transition.pred_upgrades = pred_upgrade
        declarations = [("x", INTEGER), ("flag", BOOLEAN)]
        if constant_flag:
            declarations[1] = ("flag", BOOLEAN, Value("TRUE"))
        program = Program(
            "history_validation", {"run"}, "run", declarations, [transition],
            [(Variable("u"), INTEGER), (Variable("request"), BOOLEAN)],
            [(Variable("grant"), BOOLEAN)],
            preprocess=False, is_determ=True, emit_state_binary_map=False,
        )
        program.input_format = "prog"
        return program

    def test_program_rejects_input_history_in_guards(self):
        guard = BiOp(Variable("u_prev"), ">", Value("0"))
        with self.assertRaisesRegex(ValueError, "u_prev.*transition"):
            self._program(condition=guard)

    def test_program_rejects_input_history_in_assignments(self):
        with self.assertRaisesRegex(ValueError, "u_prev.*transition"):
            self._program(action=[Update(Variable("x"), Variable("u_prev"))])

    def test_program_rejects_input_history_in_predicate_updates(self):
        upgrade = BiOp(Variable("x'"), "=", Variable("u_prev"))
        with self.assertRaisesRegex(ValueError, "u_prev.*transition"):
            self._program(pred_upgrade=upgrade)

    def test_program_rejects_state_history_everywhere_in_transitions(self):
        for name in ("x_prev", "x_prev_prev", "flag_prev"):
            history = Variable(name)
            for arguments in (
                {"condition": BiOp(history, "=", history)},
                {"action": [Update(Variable("x"), history)]},
                {"pred_upgrade": BiOp(Variable("x'"), "=", history)},
            ):
                with self.subTest(name=name, arguments=arguments):
                    with self.assertRaisesRegex(ValueError, "only allowed in LTL"):
                        self._program(**arguments)

    def test_program_rejects_history_in_transition_outputs(self):
        transition = Transition(
            "run", true(), [], [Variable("x_prev")], "run"
        )
        with self.assertRaisesRegex(ValueError, "only allowed in LTL"):
            Program(
                "history_output", {"run"}, "run", [("x", INTEGER)],
                [transition], [], [], preprocess=False, is_determ=True,
            )

    def test_native_program_and_arena_reject_lookback_but_accept_ltl_history(self):
        template = """
        {kind} history_example {{
            STATES {{ run: init }}
            ENVIRONMENT EVENTS {{ }}
            CONTROLLER EVENTS {{ }}
            VALUATION {{ x: integer := 0; }}
            TRANSITIONS {{ run -> run [{transition}] }}
            SPECIFICATION {{ X F(x_prev >= 0) }}
        }}
        """
        with patch.object(config.Config.getConfig(), "workers", 1):
            for kind in ("program", "arena"):
                for transition in (
                    "x_prev >= 0 $ x := x + 1",
                    "true $ x := x_prev",
                ):
                    with self.subTest(kind=kind, transition=transition):
                        with self.assertRaisesRegex(ValueError, "only allowed in LTL"):
                            string_to_program(template.format(kind=kind, transition=transition))

                program, spec = string_to_program(template.format(
                    kind=kind, transition="true $ x := x + 1"
                ))
                process_specifications(program, spec, None)

    def test_synthesis_rejects_history_not_rooted_in_state_variables(self):
        program = self._program()
        for spec_text in (
            "X F(u_prev > 0)",
            "X F(u_prev_prev > 0)",
            "G(request_prev)",
            "G(grant_prev)",
            "G(unknown_prev)",
        ):
            with self.subTest(spec=spec_text):
                spec = string_to_ltl_with_predicates(spec_text)
                with self.assertRaisesRegex(ValueError, "only refer to state variables"):
                    process_specifications(program, spec, None)

    def test_synthesis_accepts_numeric_and_boolean_state_history(self):
        program = self._program()
        spec = string_to_ltl_with_predicates("X F(x_prev > 0) & X G(flag_prev)")
        process_specifications(program, spec, None)

    def test_synthesis_accepts_history_of_projected_state_constants(self):
        program = self._program(constant_flag=True)
        self.assertIn(Variable("flag"), program.constants)
        spec = string_to_ltl_with_predicates("X G(flag_prev)")
        process_specifications(program, spec, None)
        with self.assertRaisesRegex(ValueError, "enclosing X"):
            process_specifications(
                program, string_to_ltl_with_predicates("G(flag_prev)"), None
            )

    def test_history_requires_a_next_ancestor_on_every_branch(self):
        program = self._program()
        for text in (
            "x_prev > 0", "G(flag_prev)", "F(x_prev > 0)",
            "X(flag_prev) & (x_prev > 0)",
            "true U (x_prev > 0)", "!(G(flag_prev))",
        ):
            with self.subTest(spec=text):
                spec = string_to_ltl_with_predicates(text)
                with self.assertRaisesRegex(ValueError, "enclosing X"):
                    process_specifications(program, spec, None)
        for text in (
            "X G(flag_prev)", "G X(flag_prev)",
            "F X(x_prev > 0)", "X F(x_prev > 0) & X(flag_prev)",
        ):
            with self.subTest(spec=text):
                process_specifications(program, string_to_ltl_with_predicates(text), None)

    def test_external_tlsf_rejects_history_without_next(self):
        with (
            patch("synthesis.synthesis.syfco_ltl", return_value="G(x_prev > 0)"),
            patch("synthesis.synthesis.syfco_ltl_in", return_value=[]),
            patch("synthesis.synthesis.syfco_ltl_out", return_value=[]),
        ):
            with self.assertRaisesRegex(ValueError, "enclosing X"):
                process_specifications(self._program(), None, "example.tlsf")

    def test_external_tlsf_specification_uses_the_same_validation(self):
        program = self._program()
        with (
            patch("synthesis.synthesis.syfco_ltl", return_value="X F(u_prev > 0)"),
            patch("synthesis.synthesis.syfco_ltl_in", return_value=[]),
            patch("synthesis.synthesis.syfco_ltl_out", return_value=[]),
        ):
            with self.assertRaisesRegex(ValueError, "u_prev.*LTL specification"):
                process_specifications(program, None, "example.tlsf")

    def test_synthesis_rejects_repeated_state_history_suffixes(self):
        program = self._program()
        for text in ("X F(x_prev_prev > 0)", "G(flag_prev_prev)"):
            with self.subTest(spec=text):
                spec = string_to_ltl_with_predicates(text)
                with self.assertRaisesRegex(ValueError, "only one _prev suffix"):
                    process_specifications(program, spec, None)

    def test_internal_source_shift_can_still_use_second_level_history(self):
        program = self._program()
        predicate = BiOp(Variable("x_prev"), ">=", Value("0"))
        shifted = predicate.prev_rep()
        program.validate_history_references(shifted, "internal source formula")
        expression, _ = shifted.to_smt(program.symbol_table)
        self.assertEqual(
            {"x_prev_prev"}, {v.symbol_name() for v in expression.get_free_variables()}
        )

    def test_external_tlsf_rejects_repeated_state_history_suffixes(self):
        program = self._program()
        with (
            patch("synthesis.synthesis.syfco_ltl", return_value="X F(x_prev_prev > 0)"),
            patch("synthesis.synthesis.syfco_ltl_in", return_value=[]),
            patch("synthesis.synthesis.syfco_ltl_out", return_value=[]),
        ):
            with self.assertRaisesRegex(ValueError, "only one _prev suffix"):
                process_specifications(program, None, "example.tlsf")
