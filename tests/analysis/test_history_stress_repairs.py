"""Regression checks for failures exposed by the history stress specifications."""

from types import SimpleNamespace
from unittest import TestCase

from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import ChainPredicate
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import StatePredicate
from analysis.abstraction.effects_abstraction.scoped_effects_update import _state_extend_effect_now_scoped
from analysis.sat_context import IncrementalSatContext
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN, INTEGER, BaseNumberTypes, Interval, Number
from prop_lang.util import conjunct, neg, sat, true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestInitialModelConjunctions(TestCase):
    def setUp(self):
        self.b, self.x = Variable("initial_b"), Variable("initial_x")
        self.symbols = {str(self.b): BOOLEAN, str(self.x): INTEGER}
        self.abstraction = EffectsAbstraction.__new__(EffectsAbstraction)
        self.abstraction.symbol_table = self.symbols
        self.abstraction.init_conf = conjunct(
            neg(self.b), BiOp(self.x, "=", Value("0"))
        )
        self.abstraction.init_state_abstraction = [[true()]]

    def test_adding_boolean_predicate_removes_true_placeholder(self):
        models = self.abstraction.update_init_abstraction_state_pred(
            StatePredicate(self.b, False)
        )
        self.assertEqual([[neg(self.b)]], models)

    def test_new_numeric_chain_preserves_existing_boolean_initial_condition(self):
        for model in ([true(), neg(self.b)], [neg(self.b)]):
            with self.subTest(model=model):
                self.abstraction.init_state_abstraction = [model]
                chain = ChainPredicate(
                    self.x, SimpleNamespace(symbol_table=self.symbols, inp_out_puts=[]),
                    False,
                )
                chain.add_predicate([BiOp(self.x, "<=", Value("0"))])
                models = self.abstraction.update_init_abstraction_new_chain_pred(chain)
                self.assertEqual(1, len(models))
                self.assertIn(neg(self.b), models[0])
                self.assertFalse(any(isinstance(f, Value) and f.is_true() for f in models[0]))


class TestNonbinaryInputDependencies(TestCase):
    def test_input_source_regions_determine_assignment_results(self):
        i, x = Variable("source_input"), Variable("assigned_x")
        bounded = Number(BaseNumberTypes.integer, Interval("0", "2"))
        symbols = {str(v): bounded for v in (i, i.prev_rep(), x)}
        predicate = BiOp(i, "<=", Value("1"))
        result_predicate = BiOp(x, "<=", Value("1"))
        source = StatePredicate(predicate, True)
        gu = BiOp(x, "=", i.prev_rep())
        before = [(true(), [result_predicate, neg(result_predicate)])]
        for scoped in (False, True):
            with self.subTest(scoped=scoped):
                if scoped:
                    with IncrementalSatContext(symbols, gu) as context:
                        effects = _state_extend_effect_now_scoped(source, before, context)
                else:
                    effects = source.extend_effect_now(gu, before, symbols)
                self.assertEqual(2, len(effects))
                for now, nexts in effects:
                    expected = result_predicate if now == predicate else neg(result_predicate)
                    self.assertEqual(1, len(nexts))
                    self.assertFalse(sat(conjunct(nexts[0], neg(expected)), symbols))
