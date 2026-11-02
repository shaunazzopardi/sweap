from types import SimpleNamespace
from unittest import TestCase

from programs.issy_export import IssyPrinter, program_to_issy, restore_next_predicates
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestIssyHistoryExport(TestCase):
    def setUp(self):
        self.x = Variable("x")
        self.previous_x = Variable("x_prev")
        self.current_names = {"x", "y", "event", "mini"}

    def restore(self, formula, controls=None):
        return restore_next_predicates(formula, self.current_names, controls or set())

    def test_all_relations_restore_both_time_indices(self):
        for operator in ("=", "!=", "<", "<=", ">", ">="):
            with self.subTest(operator=operator):
                formula = UniOp("X", BiOp(self.x, operator, self.previous_x))
                self.assertEqual(
                    self.restore(formula), BiOp(Variable("x'"), operator, self.x)
                )
                self.assertNotIn("x'", str(formula))

    def test_arithmetic_and_boolean_expression(self):
        body = BiOp(
            MathExpr(BiOp(BiOp(self.x, "+", Value(1)), ">", self.previous_x)),
            "&",
            UniOp("!", BiOp(Variable("y_prev"), "<=", Variable("y"))),
        )
        expected = BiOp(
            MathExpr(BiOp(BiOp(Variable("x'"), "+", Value(1)), ">", self.x)),
            "&",
            UniOp("!", BiOp(Variable("y"), "<=", Variable("y'"))),
        )
        self.assertEqual(self.restore(UniOp("X", body)), expected)

    def test_next_over_minigame_until_keeps_the_gate_and_shifts_it(self):
        mini = Variable("mini")
        predicate = BiOp(self.x, "!=", self.previous_x)
        body = BiOp(mini, "U", BiOp(UniOp("!", mini), "&", predicate))
        expected = BiOp(
            Variable("mini'"), "U",
            BiOp(
                UniOp("!", Variable("mini'")), "&",
                BiOp(Variable("x'"), "!=", self.x),
            ),
        )
        self.assertEqual(self.restore(UniOp("X", body)), expected)

    def test_temporal_expression_is_not_limited_to_an_equality_atom(self):
        formula = UniOp("X", UniOp("G", BiOp(self.x, ">", self.previous_x)))
        self.assertEqual(
            self.restore(formula), UniOp("G", BiOp(Variable("x'"), ">", self.x))
        )

    def test_only_one_of_two_next_operators_is_removed(self):
        formula = UniOp("X", UniOp("X", BiOp(self.x, ">", self.previous_x)))
        self.assertEqual(
            self.restore(formula), UniOp("X", BiOp(Variable("x'"), ">", self.x))
        )

    def test_unrelated_next_and_declared_previous_named_variables_are_unchanged(self):
        ordinary = UniOp("X", BiOp(self.x, ">", Value(0)))
        self.assertIs(self.restore(ordinary), ordinary)
        actual_previous_name = UniOp("X", BiOp(self.x, ">", self.previous_x))
        self.assertIs(
            restore_next_predicates(
                actual_previous_name, {"x", "x_prev"}, set()
            ),
            actual_previous_name,
        )

    def test_previous_input_reference_becomes_current_input(self):
        formula = UniOp("X", BiOp(self.x, ">=", Variable("event_prev")))
        self.assertEqual(
            self.restore(formula), BiOp(Variable("x'"), ">=", Variable("event"))
        )

    def test_current_controller_reference_retains_its_next_operator(self):
        event = Variable("event")
        formula = UniOp("X", BiOp(event, "&", BiOp(self.x, ">", self.previous_x)))
        expected = BiOp(UniOp("X", event), "&", BiOp(Variable("x'"), ">", self.x))
        restored = self.restore(formula, {"event"})
        self.assertEqual(restored, expected)
        printer = IssyPrinter(
            {"x": INTEGER, "event": BOOLEAN}, controller_props={"event"}
        )
        self.assertEqual(printer.formula(restored), "(X([event']) && [x' > x])")

    def test_existing_primed_branch_is_not_double_primed(self):
        primed = BiOp(Variable("y'"), "=", Variable("y"))
        formula = UniOp("X", BiOp(BiOp(self.x, ">", self.previous_x), "&", primed))
        self.assertEqual(
            self.restore(formula),
            BiOp(BiOp(Variable("x'"), ">", self.x), "&", UniOp("X", primed)),
        )

    def test_current_input_reference_keeps_its_temporal_next(self):
        event = Variable("event")
        formula = UniOp("X", BiOp(event, "&", BiOp(self.x, ">", self.previous_x)))
        restored = restore_next_predicates(
            formula, self.current_names, set(), {"event"}
        )
        self.assertEqual(
            restored,
            BiOp(UniOp("X", event), "&", BiOp(Variable("x'"), ">", self.x)),
        )

    def test_export_restores_predicate_without_adding_history_state(self):
        program = SimpleNamespace(
            states={"q0", "mini"}, initial_state="q0",
            symbol_table={"x": INTEGER, "x_prev": INTEGER, "mini": BOOLEAN},
            env_events=[], con_events=[], local_vars=[self.x], init_var_values={},
            transitions=[Transition("q0", true(), [], [], "q0")],
        )
        body = BiOp(
            Variable("mini"), "U",
            BiOp(UniOp("!", Variable("mini")), "&", BiOp(self.x, ">", self.previous_x)),
        )
        text = program_to_issy(program, UniOp("X", body))
        self.assertIn("assert ([mini'] U (!([mini']) && [x' > x]))", text)
        self.assertIn("state bool mini", text)
        self.assertNotIn("x_prev", text)

    def test_projected_constant_history_is_also_replaced(self):
        program = SimpleNamespace(
            states={"q0"}, initial_state="q0", symbol_table={},
            env_events=[], con_events=[], local_vars=[], init_var_values={},
            constants={self.x: Value(4)},
            transitions=[Transition("q0", true(), [], [], "q0")],
        )
        text = program_to_issy(
            program, UniOp("X", BiOp(self.x, "=", self.previous_x))
        )
        self.assertIn("assert X([4 = 4])", text)
        self.assertNotIn("x_prev", text)
