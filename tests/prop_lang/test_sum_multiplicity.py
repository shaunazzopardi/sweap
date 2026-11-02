from itertools import permutations
from unittest import TestCase

from parsing.util.partitioned_update_chain import (
    _canonical_update_predicate_keys,
    build_partitioned_update_chain,
    build_update_predicate_guard_replacements,
)
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import is_tautology, sum as formula_sum
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestSumMultiplicity(TestCase):
    def test_repeated_terms_and_cancellation(self):
        y = Variable("y")
        minus_y = UniOp("-", y)
        for terms, expected in (
            ([y, y], BiOp(y, "+", y)),
            ([y, y, minus_y], y),
            ([y, minus_y, minus_y], minus_y),
            ([y, y, minus_y, minus_y], Value("0")),
            ([Value("2"), Value("2")], Value("4")),
            ([Value("2"), Value("2"), Value("-2")], Value("2")),
        ):
            with self.subTest(terms=terms):
                self.assertTrue(is_tautology(
                    BiOp(formula_sum(terms), "=", expected), {"y": INTEGER}
                ))

    def test_cancellation_is_independent_of_order(self):
        x, y = Variable("x"), Variable("y")
        for terms in set(permutations((x, y, y, UniOp("-", y)))):
            with self.subTest(terms=terms):
                self.assertTrue(is_tautology(
                    BiOp(formula_sum(terms), "=", BiOp(x, "+", y)),
                    {"x": INTEGER, "y": INTEGER},
                ))

    def test_canonical_keys_distinguish_y_from_y_plus_y(self):
        x, y = Variable("x"), Variable("y")
        single = set(_canonical_update_predicate_keys(Update(x, y)))
        double = set(_canonical_update_predicate_keys(Update(x, BiOp(y, "+", y))))
        self.assertFalse(single & double)

    def test_canonical_keys_preserve_cancelled_multiplicity(self):
        x, y = Variable("x"), Variable("y")
        update = Update(x, BiOp(BiOp(y, "+", y), "-", y))
        self.assertIn("(x' = y)", _canonical_update_predicate_keys(update))

    def test_update_guard_replacement_keeps_distinct_choices(self):
        x, y = Variable("x"), Variable("y")
        single = Update(x, y)
        double = Update(x, BiOp(y, "+", y))
        chain = build_partitioned_update_chain({"x": {single, double}}, {y})
        replacements = build_update_predicate_guard_replacements(
            [double], chain.update_predicate_key_to_guard,
        )
        symbols = {str(v): BOOLEAN for v in chain.controller_events}
        for transition in chain.transitions:
            matches = double in transition.action
            guard = BiOp(replacements[double], "<->", transition.condition)
            self.assertEqual(matches, is_tautology(guard, symbols))
