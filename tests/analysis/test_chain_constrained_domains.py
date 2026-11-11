"""Constrained numeric domains must not yield empty abstract choices."""

from itertools import permutations, product
from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import ChainPredicate
from prop_lang.biop import BiOp
from prop_lang.types.types import (
    BOOLEAN, INTEGER, NATURAL, BaseNumberTypes, Interval, Number,
)
from prop_lang.util import conjunct, neg, sat
from prop_lang.value import Value
from prop_lang.variable import Variable


MODULE = "analysis.abstraction.effects_abstraction.predicates.ChainPredicate"


class TestChainConstrainedDomains(TestCase):
    def chain(self, term, symbols):
        program = SimpleNamespace(symbol_table=symbols, inp_out_puts=[])
        return ChainPredicate(term, program, False)

    def assert_exact(self, chain, symbols, values):
        for interval in chain.choices():
            self.assertTrue(sat(interval, symbols), str(interval))
        # Every bit valuation denotes exactly one inhabited interval.
        for bits in product((False, True), repeat=len(chain.bin_vars)):
            valuation = dict(zip(chain.bin_vars, (Value(str(b).upper()) for b in bits)))
            self.assertEqual(
                1,
                sum(
                    sat(rep.replace_vars(valuation), {})
                    for rep in chain.bin_rep.values()
                ),
            )
        for value in values:
            point = BiOp(chain.term, "=", Value(str(value)))
            interval = next(p for p in chain.chain if sat(conjunct(point, p), symbols))
            for predicate in chain.raw_state_preds:
                expected = sat(conjunct(point, predicate), symbols)
                representation = chain.boolean_rep()[predicate]
                wrong = neg(representation) if expected else representation
                self.assertFalse(sat(
                    conjunct(chain.bin_rep[interval], wrong),
                    {str(v): BOOLEAN for v in chain.bin_vars},
                ))

    def test_natural_history_excludes_empty_negative_interval(self):
        x = Variable("y_prev")
        symbols = {str(x): NATURAL}
        for bounds in permutations((-1, 0, 2)):
            with self.subTest(bounds=bounds):
                chain = self.chain(x, symbols)
                for bound in bounds:
                    chain.add_predicate([BiOp(x, "<=", Value(str(bound)))])
                    self.assert_exact(chain, symbols, range(5))
                    if isinstance(chain.old_to_new, dict):
                        self.assertTrue(all(
                            q in chain.chain
                            for choices in chain.old_to_new.values()
                            for q in choices
                        ))
                self.assertEqual(3, len(chain.chain))

    def test_bounded_domain_removes_both_empty_ends(self):
        x = Variable("bounded_x")
        symbols = {str(x): Number(BaseNumberTypes.integer, Interval("0", "2"))}
        chain = self.chain(x, symbols)
        chain.add_predicate([BiOp(x, "<=", Value(str(n))) for n in (-1, 0, 2, 5)])
        self.assertEqual(2, len(chain.chain))
        self.assert_exact(chain, symbols, range(3))

    def test_single_inhabited_interval_needs_no_bits(self):
        x = Variable("natural_x")
        symbols = {str(x): NATURAL}
        chain = self.chain(x, symbols)
        impossible = BiOp(x, "<=", Value("-1"))
        chain.add_predicate([impossible])
        self.assertEqual([], chain.bin_vars)
        self.assertTrue(chain.boolean_rep()[impossible].is_false())
        self.assert_exact(chain, symbols, range(3))

    def test_unbounded_integer_terms_skip_domain_validation(self):
        x = Variable("integer_x")
        chain = self.chain(x, {str(x): INTEGER})
        with patch(
            f"{MODULE}.sat", side_effect=AssertionError("unexpected domain check")
        ):
            chain.add_predicate([
                BiOp(x, "<=", Value("-1")), BiOp(x, "<=", Value("0")),
            ])

    def test_refinement_reuses_unchanged_interval_validation(self):
        x = Variable("refined_natural")
        chain = self.chain(x, {str(x): NATURAL})
        chain.add_predicate([BiOp(x, "<=", Value("0"))])
        with patch(f"{MODULE}.sat", wraps=sat) as validate:
            chain.add_predicate([BiOp(x, "<=", Value("2"))])
        self.assertEqual(2, validate.call_count)

    def test_composite_term_uses_constrained_variable_domains(self):
        x, y = Variable("natural_left"), Variable("natural_right")
        term = BiOp(x, "+", y)
        chain = self.chain(term, {str(x): NATURAL, str(y): NATURAL})
        chain.add_predicate([BiOp(term, "<=", Value("-1")), BiOp(term, "<=", Value("0"))])
        self.assertEqual(2, len(chain.chain))
        self.assert_exact(chain, chain.program.symbol_table, range(4))
