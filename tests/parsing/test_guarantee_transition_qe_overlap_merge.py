import unittest
from time import perf_counter
from unittest.mock import patch

from parsing import string_to_issy as string_to_issy_module
from parsing.util.game_transition_utils import determinise
from programs.binary_rep_map import BinaryRepMap
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set
from prop_lang.util import is_tautology, sat
from prop_lang.types.types import INTEGER, BOOLEAN
from prop_lang.update import Update
from prop_lang.value import Value
from prop_lang.variable import Variable
from prop_lang.util import neg


class TestGuaranteeTransitionQeOverlapMerge(unittest.TestCase):
    @staticmethod
    def _build_overlap_transitions():
        q = Variable("q")
        y = Variable("y")

        t_pos = Transition(
            "eval",
            BiOp(y, ">=", Value(0)),
            [Update(q, BiOp(BiOp(q, "+", y), "+", Value(-1)))],
            [],
            "eval",
        )
        t_neg = Transition(
            "eval",
            BiOp(y, "<=", Value(0)),
            [Update(q, BiOp(BiOp(q, "-", y), "+", Value(-1)))],
            [],
            "eval",
        )
        return q, y, t_pos, t_neg

    def test_merges_overlap_when_updates_qe_equivalent_under_guard(self):
        q, y, t_pos, t_neg = self._build_overlap_transitions()

        merged, merge_count = (
            string_to_issy_module._merge_extracted_transitions_with_qe_equivalent_overlaps(
                [t_pos, t_neg],
                {"q": INTEGER, "y": INTEGER},
            )
        )

        self.assertEqual(merge_count, 1)
        self.assertEqual(len(merged), 3)

        symbol_table = {"q": INTEGER, "y": INTEGER}
        eq_zero = BiOp(y, "=", Value(0))
        gt_zero = BiOp(y, ">", Value(0))
        lt_zero = BiOp(y, "<", Value(0))

        guards = [t.condition for t in merged]
        self.assertTrue(
            any(
                is_tautology(BiOp(g, "->", eq_zero), symbol_table)
                and sat(g, symbol_table)
                for g in guards
            )
        )
        self.assertTrue(
            any(
                is_tautology(BiOp(g, "->", gt_zero), symbol_table)
                and sat(g, symbol_table)
                for g in guards
            )
        )
        self.assertTrue(
            any(
                is_tautology(BiOp(g, "->", lt_zero), symbol_table)
                and sat(g, symbol_table)
                for g in guards
            )
        )
        union_guard = guards[0]
        for g in guards[1:]:
            union_guard = BiOp(union_guard, "|", g)
        self.assertFalse(sat(neg(union_guard), symbol_table))

    def test_merge_reduces_booleanisation_helpers(self):
        _, _, t_pos, t_neg = self._build_overlap_transitions()
        symbol_table = {"q": INTEGER, "y": INTEGER}

        _, con_vars_before = determinise(
            {"eval": [t_pos, t_neg]},
            "formula",
            dict(symbol_table),
        )
        self.assertGreater(len(con_vars_before), 0)

        merged, _ = (
            string_to_issy_module._merge_extracted_transitions_with_qe_equivalent_overlaps(
                [t_pos, t_neg],
                symbol_table,
            )
        )
        _, con_vars_after = determinise(
            {"eval": merged},
            "formula",
            dict(symbol_table),
        )
        self.assertEqual(len(con_vars_after), 0)

    def _assert_pairwise_disjoint(self, transitions: list[Transition], symbol_table):
        for i, t_i in enumerate(transitions):
            for t_j in transitions[i + 1 :]:
                if t_i.src != t_j.src:
                    continue
                self.assertFalse(
                    sat(BiOp(t_i.condition, "&", t_j.condition), symbol_table),
                    msg=f"non-disjoint guards:\n{t_i}\n{t_j}",
                )

    def _profile_determinise(
        self,
        raw_transitions: dict[str, list[Transition]],
        symbol_table: dict[str, object],
        label: str,
    ):
        for trans in raw_transitions.values():
            for t in trans:
                self.assertEqual(t.src, t.tgt, msg="comparison assumes stutter target")

        with patch.object(
            BinaryRepMap,
            "_normalise_boolean_formula",
            autospec=True,
            side_effect=lambda _self, f: f,
        ):
            start = perf_counter()
            transitions, con_vars = determinise(
                raw_transitions,
                "formula",
                dict(symbol_table),
            )
            elapsed = perf_counter() - start

        sem_symbol_table = dict(symbol_table)
        sem_symbol_table.update({str(v): BOOLEAN for v in set(con_vars)})
        self._assert_pairwise_disjoint(transitions, sem_symbol_table)

        print(
            f"\nDeterminisation profile ({label}):"
            f" transitions={len(transitions)}"
            f" time={elapsed:.6f}s helpers={len(con_vars)}"
        )

    def test_region_local_determinisation_profile_small_overlap(self):
        _, _, t_pos, t_neg = self._build_overlap_transitions()
        raw_transitions = {"eval": [t_pos, t_neg]}
        symbol_table = {"q": INTEGER, "y": INTEGER}
        self._profile_determinise(raw_transitions, symbol_table, "small-overlap")

    @staticmethod
    def _build_complex_overlap_transitions():
        # Counter-game-style overlap: boolean selector guards with i=0 fallback
        # disjuncts that create heavy guard overlap across updates.
        a = Variable("formula_con_act_0")
        b = Variable("formula_con_act_1")
        c = Variable("formula_con_act_2")
        i = Variable("i")
        x0 = Variable("x0")
        x1 = Variable("x1")

        def up(lhs, rhs):
            return [Update(lhs, rhs)]

        def AND(*xs):
            return conjunct_formula_set(xs)

        def OR(*xs):
            return disjunct_formula_set(xs)

        i_eq_0 = BiOp(i, "=", Value(0))
        g1 = OR(AND(neg(a), neg(b), neg(c)), AND(i_eq_0, OR(a, b)))
        g2 = OR(AND(neg(a), b, neg(c)), AND(i_eq_0, AND(neg(b), c)))
        g3 = OR(AND(a, neg(b), neg(c)), AND(i_eq_0, AND(neg(a), c)))
        g4 = OR(AND(neg(a), neg(b), c), AND(i_eq_0, AND(a, b)))
        g5 = OR(AND(a, b), AND(a, c), AND(i_eq_0, AND(neg(a), neg(b))))

        transitions = [
            Transition("eval", g1, up(x0, BiOp(x0, "+", Value(1))), [], "eval"),
            Transition(
                "eval",
                g2,
                up(x0, BiOp(BiOp(x0, "+", Value(1)), "+", i)),
                [],
                "eval",
            ),
            Transition("eval", g3, up(x0, Value(0)), [], "eval"),
            Transition("eval", g4, up(x1, BiOp(x1, "+", Value(1))), [], "eval"),
            Transition(
                "eval",
                g5,
                up(x1, BiOp(BiOp(x1, "+", Value(1)), "+", i)),
                [],
                "eval",
            ),
        ]
        symbol_table = {
            "formula_con_act_0": BOOLEAN,
            "formula_con_act_1": BOOLEAN,
            "formula_con_act_2": BOOLEAN,
            "i": INTEGER,
            "x0": INTEGER,
            "x1": INTEGER,
        }
        return transitions, symbol_table

    def test_region_local_determinisation_profile_complex_counter_overlap(self):
        transitions, symbol_table = self._build_complex_overlap_transitions()
        raw_transitions = {"eval": transitions}
        self._profile_determinise(
            raw_transitions, symbol_table, "complex-counter-overlap"
        )

    @staticmethod
    def _build_complex_arithmetic_overlap_transitions():
        q = Variable("q")
        r = Variable("r")
        x = Variable("x")
        y = Variable("y")

        def up(lhs, rhs):
            return [Update(lhs, rhs)]

        transitions = [
            Transition(
                "eval",
                BiOp(x, ">=", Value(0)),
                up(q, BiOp(q, "+", Value(1))),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(x, "<=", Value(0)),
                up(q, BiOp(q, "+", Value(-1))),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(y, ">=", Value(0)),
                up(r, BiOp(r, "+", Value(1))),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(y, "<=", Value(0)),
                up(r, BiOp(r, "+", Value(-1))),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(BiOp(x, "+", y), ">=", Value(0)),
                up(q, BiOp(q, "+", y)),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(BiOp(x, "-", y), ">=", Value(0)),
                up(q, BiOp(q, "-", y)),
                [],
                "eval",
            ),
            Transition("eval", BiOp(x, "=", Value(0)), up(q, q), [], "eval"),
            Transition("eval", BiOp(y, "=", Value(0)), up(r, r), [], "eval"),
            Transition(
                "eval",
                BiOp(BiOp(x, ">=", Value(0)), "&", BiOp(y, ">=", Value(0))),
                up(q, BiOp(q, "+", Value(2))),
                [],
                "eval",
            ),
            Transition(
                "eval",
                BiOp(BiOp(x, "<=", Value(0)), "&", BiOp(y, "<=", Value(0))),
                up(q, BiOp(q, "+", Value(-2))),
                [],
                "eval",
            ),
        ]
        symbol_table = {"q": INTEGER, "r": INTEGER, "x": INTEGER, "y": INTEGER}
        return transitions, symbol_table

    def test_region_local_determinisation_profile_complex_arithmetic_overlap(self):
        transitions, symbol_table = self._build_complex_arithmetic_overlap_transitions()
        raw_transitions = {"eval": transitions}
        self._profile_determinise(
            raw_transitions, symbol_table, "complex-arithmetic-overlap"
        )


if __name__ == "__main__":
    unittest.main()
