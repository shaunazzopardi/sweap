from unittest import TestCase

from analysis.abstraction.effects_abstraction.effects_abstraction import (
    _invariant_has_prev_vars,
)
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import StatePredicate
from analysis.compatibility_checking.compatibility_builder import (
    _partition_state_and_transition_predicates,
)
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.util import stringify_pred
from prop_lang.value import Value
from prop_lang.variable import Variable
from programs.minigame_filler import MinigameFiller


class TestHistorySuffixDetection(TestCase):
    def test_only_a_variable_suffix_marks_history(self):
        for name, expected in (
            ("counter_preview", False), ("previous_count", False),
            ("x_prev_y", False), ("x_prev", True), ("x_prev_prev", True),
        ):
            with self.subTest(name=name):
                pred = BiOp(Variable(name), "<=", Value("0"))
                self.assertEqual(expected, Variable(name).is_prev())
                self.assertEqual(expected, pred.has_prev_vars())
                wrapped = StatePredicate(pred, False)
                self.assertEqual(expected, wrapped.has_prev_vars())
                states, transitions = _partition_state_and_transition_predicates(
                    {wrapped}, set()
                )
                self.assertEqual(expected, wrapped in transitions)
                self.assertEqual(not expected, wrapped in states)
                self.assertEqual(expected, _invariant_has_prev_vars(stringify_pred(pred)))

    def test_history_type_lookup_preserves_underscores_in_the_base_name(self):
        for name in ("counter_preview_prev", "counter_preview_prev_prev"):
            with self.subTest(name=name):
                expr, _ = Variable(name).to_smt({"counter_preview": INTEGER})
                self.assertEqual(name, expr.symbol_name())

    def test_minigame_variable_collection_only_strips_suffixes(self):
        formula = BiOp(Variable("counter_preview_prev"), "=", Variable("counter_preview"))
        self.assertEqual(
            {Variable("counter_preview")}, MinigameFiller._collect_ltl_vars([formula])
        )
