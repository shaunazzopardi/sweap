from types import SimpleNamespace
from unittest import TestCase

from analysis.abstraction.effects_abstraction.abs_util import update_var_partition_mult
from analysis.abstraction.effects_abstraction.effects_abstraction import update_effects
from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import ChainPredicate
from analysis.abstraction.effects_abstraction.predicates.StatePredicate import StatePredicate
from analysis.abstraction.effects_abstraction.predicates.TransitionPredicate import (
    TransitionPredicate,
)
from analysis.sat_context import IncrementalSatContext, NonIncrementalSatContext
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import conjunct, disjunct_formula_set, neg, sat, true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestPureHistoryEffectSelection(TestCase):
    def test_mixed_history_uses_bounds_on_the_source_variable(self):
        for use_chain in (False, True):
            with self.subTest(chain=use_chain):
                x, y, y_prev = map(Variable, ("mixed_x", "mixed_y", "mixed_y_prev"))
                variables = [x, y, y_prev, x.prev_rep(), y_prev.prev_rep()]
                symbols = {str(v): INTEGER for v in variables}
                program = SimpleNamespace(inp_out_puts=[], symbol_table=symbols)
                source_bound = BiOp(y, "<=", Value("-1"))
                term = BiOp(x, "-", y_prev)
                mixed = BiOp(term, "<=", Value("0"))
                if use_chain:
                    source_pred = ChainPredicate(y, program, False)
                    source_pred.add_predicate([source_bound])
                    history_pred = ChainPredicate(term, program, False)
                    history_pred.add_predicate([mixed])
                else:
                    source_pred = StatePredicate(source_bound, False)
                    history_pred = StatePredicate(mixed, False)
                predicates = {source_pred, history_pred}
                partitions, index, var_partitions = update_var_partition_mult(
                    predicates,
                    {i: {v} for i, v in enumerate(variables)},
                    {v: set() for v in variables},
                    {v: i for i, v in enumerate(variables)},
                )
                updates = [Update(x, Value("0")), Update(y, y)]
                gu = conjunct(BiOp(x, "=", Value("0")), BiOp(y, "=", y_prev))
                current = (set(), set())
                effects = update_effects(
                    [(true(), [true()])], updates, gu, current, predicates,
                    partitions, var_partitions, index, set(), {source_pred}, symbols,
                )
                self.assertIn(source_pred, current[0])
                self.assertIn(history_pred, current[1])
                for now, nexts in effects:
                    for nxt in nexts:
                        if sat(conjunct(now, source_bound), symbols):
                            self.assertFalse(sat(conjunct(nxt, mixed), symbols))
                        if sat(conjunct(now, neg(source_bound)), symbols):
                            self.assertFalse(sat(conjunct(nxt, neg(mixed)), symbols))
                effect = disjunct_formula_set(
                    conjunct(now.prev_rep(), nxt)
                    for now, nexts in effects for nxt in nexts
                )
                self.assertFalse(sat(conjunct(gu, neg(effect)), symbols))

    def test_history_lookup_is_limited_to_the_update_partition(self):
        for mode in ("increment", "identity", "constant"):
            for context_cls in (IncrementalSatContext, NonIncrementalSatContext):
                with self.subTest(mode=mode, context=context_cls):
                    self._check_selection(mode, context_cls)

    def test_constant_update_uses_current_predicate_added_by_refinement(self):
        for context_cls in (IncrementalSatContext, NonIncrementalSatContext):
            with self.subTest(context=context_cls):
                self._check_selection("constant", context_cls, late_current=True)

    def _check_selection(self, mode, context_cls, late_current=False):
        program = SimpleNamespace(inp_out_puts=[])

        def chain(name):
            pred = ChainPredicate(Variable(name), program, False)
            pred.add_predicate([BiOp(Variable(name), "<=", Value("0"))])
            return pred

        current_x, history_x, history_y = map(chain, ("x", "x_prev", "y_prev"))
        # A transition wrapper indexed under x_prev has the same source dependency.
        transition_pred = TransitionPredicate(
            [BiOp(Variable("x_prev"), "<=", Value("0"))], False
        )
        preds = {current_x, history_x, history_y, transition_pred}
        initial_preds = preds - {current_x} if late_current else preds
        variables = [Variable(v) for v in ("x", "y", "x_prev", "y_prev")]
        partitions, v_to_preds, v_to_partition = update_var_partition_mult(
            initial_preds,
            {i: {v} for i, v in enumerate(variables)},
            {v: set() for v in variables},
            {v: i for i, v in enumerate(variables)},
        )
        symbols = {v.name: INTEGER for v in variables}
        symbols.update({"x_prev_prev": INTEGER, "y_prev_prev": INTEGER})
        right, relation = {
            "identity": (Variable("x"), "x = x_prev"),
            "increment": (BiOp(Variable("x"), "+", Value("1")), "x = x_prev + 1"),
            "constant": (Value("0"), "x = 0"),
        }[mode]
        update = Update(Variable("x"), right)
        gu = string_to_prop(relation)
        # The caller handles a reset's postcondition, or an identity's
        # invariant, separately. Neither puts current_x into next_preds.
        ignore_in_nexts = {current_x} if mode in ("constant", "identity") else set()
        current_preds = (set(), set())
        effects = [(true(), [true()])]
        batches = [initial_preds, {current_x}] if late_current else [preds]
        for new_preds in batches:
            if late_current and new_preds == {current_x}:
                partitions, v_to_preds, v_to_partition = update_var_partition_mult(
                    new_preds, partitions, v_to_preds, v_to_partition
                )
            with context_cls(symbols, gu) as sat_ctx:
                effects = update_effects(
                    effects, [update], gu, current_preds, new_preds,
                    partitions, v_to_partition, v_to_preds, set(), ignore_in_nexts,
                    symbols,
                    sat_ctx=sat_ctx,
                )
        self.assertIn(history_x, current_preds[1])
        self.assertNotIn(history_y, current_preds[1])
        self.assertIn(transition_pred, current_preds[1])
        # The emitted cases must connect the source's x region to the
        # destination's x_prev region, even when x := 0 has no RHS variables.
        source_region = BiOp(Variable("x"), "<=", Value("0"))
        history_region = BiOp(Variable("x_prev"), "<=", Value("0"))
        for now, nexts in effects:
            for nxt in nexts:
                if sat(conjunct(now, source_region), symbols):
                    self.assertFalse(sat(conjunct(nxt, neg(history_region)), symbols))
                if sat(conjunct(now, neg(source_region)), symbols):
                    self.assertFalse(sat(conjunct(nxt, history_region), symbols))
        effect = disjunct_formula_set(
            conjunct(now.prev_rep(), nxt)
            for now, nexts in effects for nxt in nexts
        )
        self.assertFalse(sat(conjunct(gu, neg(effect)), symbols))
        # This valid step changes the history region from <=0 to >0.
        witness = string_to_prop("x_prev = 1 & x_prev_prev = 0")
        self.assertTrue(sat(conjunct(conjunct(gu, witness), effect), symbols))
