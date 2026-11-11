from itertools import permutations
from types import SimpleNamespace
from unittest import TestCase

from analysis.abstraction.effects_abstraction.predicates.ChainPredicate import ChainPredicate
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN
from prop_lang.util import conjunct, neg, sat
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestChainIntegerBounds(TestCase):
    def test_adjacent_large_integer_cuts_preserve_the_middle_region(self):
        for bounds in ((2**53, 2**53 + 1), (-2**53 - 1, -2**53)):
            for order in permutations(bounds):
                with self.subTest(bounds=bounds, order=order):
                    x = Variable("large_bound_x")
                    predicates = {b: BiOp(x, "<=", Value(str(b))) for b in bounds}
                    chain = ChainPredicate(x, SimpleNamespace(inp_out_puts=[]), False)
                    for bound in order:
                        chain.add_predicate([predicates[bound]])
                    self.assertEqual(
                        list(bounds), [int(str(p.right)) for p in chain.raw_state_preds]
                    )
                    representations = chain.boolean_rep()
                    middle = conjunct(
                        neg(representations[predicates[bounds[0]]]),
                        representations[predicates[bounds[1]]],
                    )
                    self.assertTrue(sat(middle, {str(v): BOOLEAN for v in chain.bin_vars}))
