import unittest
from time import perf_counter

import config

from tests.parsing._legacy_sat_guided_transition_utils import (
    extract_updates_from_formula,
    generate_update_combinations,
    handle_update_combination,
    handle_update_partition,
)

from parsing.string_to_ltl import string_to_issy_ltl
from prop_lang.util import (
    conjunct,
    conjunct_formula_set,
    disjunct_formula_set,
    iff,
    is_tautology,
    false,
    strip_mathexpr,
)
from prop_lang.types.types import INTEGER


class TestIssyUpdateCombinationSoundness(unittest.TestCase):
    def setUp(self):
        self._config = config.Config.getConfig()
        self._prev_workers = self._config.workers
        self._config.workers = 1

    def tearDown(self):
        self._config.workers = self._prev_workers

    def test_update_combinations_keep_conjunctive_same_var_constraints(self):
        symbol_table = {
            "x": INTEGER,
            "x'": INTEGER,
        }
        cond = string_to_issy_ltl("TRUE")
        u1 = strip_mathexpr(string_to_issy_ltl("(x' <= 1)"))
        u2 = strip_mathexpr(string_to_issy_ltl("(x' >= 0)"))

        combos = generate_update_combinations(
            cond=cond,
            updates={u1, u2},
            inputs=set(),
            symbol_table=symbol_table,
        )

        combo_as_str = {
            frozenset(str(u) for u in updates)
            for item in combos
            if item is not None
            for _, updates in [item]
        }
        self.assertIn(frozenset({"(x' <= 1)", "(x' >= 0)"}), combo_as_str)

    @staticmethod
    def _counter_style_formula(num_counters: int, bound: int) -> str:
        clauses = []
        clauses.append(
            "(" + " | ".join(f"(d' = {j})" for j in range(num_counters + 1)) + ")"
        )
        for k in range(1, num_counters + 1):
            clauses.append(
                f"((!(x{k} = {bound})) -> (((x{k-1}' = (x{k-1} + 1)) & "
                f"(!(d' = {k-1}) | (i > 1) | (i < -1))) | "
                f"((x{k-1}' = ((x{k-1} + 1) + i)) & (d' = {k-1}))))"
            )
            clauses.append(f"((x{k} = {bound}) -> (x{k-1}' = 0))")
        clauses.append(
            f"(((x{num_counters}' = (x{num_counters} + 1)) & "
            f"(!(d' = {num_counters}) | (i > 1) | (i < -1))) | "
            f"((x{num_counters}' = ((x{num_counters} + 1) + i)) & "
            f"(d' = {num_counters})))"
        )
        return "(" + " & ".join(clauses) + ")"

    @staticmethod
    def _combos_to_formula(combos):
        disjuncts = []
        for cond, updates in combos:
            disjuncts.append(conjunct(cond, conjunct_formula_set(list(updates))))
        if len(disjuncts) == 0:
            return false()
        return disjunct_formula_set(disjuncts)

    def _run_generate(self, cond, updates, symbol_table):
        return generate_update_combinations(
            cond=cond,
            updates=updates,
            inputs=set(),
            symbol_table=symbol_table,
        )

    @staticmethod
    def _run_legacy_baseline(cond, updates, symbol_table):
        update_list = list(updates)
        combos = handle_update_partition(updates, symbol_table)
        return [
            handle_update_combination((combo, cond, update_list, set(), symbol_table))
            for combo in combos
        ]

    def test_generate_matches_legacy_baseline_on_counter_style_formulas(self):
        symbol_table = {"i": INTEGER, "d": INTEGER}
        for i in range(0, 6):
            symbol_table[f"x{i}"] = INTEGER
            symbol_table[f"x{i}'"] = INTEGER
        symbol_table["d'"] = INTEGER

        formulas = [
            self._counter_style_formula(2, 10),
            self._counter_style_formula(3, 7),
        ]

        timings = []
        for formula_text in formulas:
            formula = string_to_issy_ltl(formula_text)
            updates, replacements = extract_updates_from_formula(formula)
            cond = formula.replace_formulas(replacements)

            start = perf_counter()
            generate_rs = self._run_generate(cond, updates, symbol_table)
            generate_time = perf_counter() - start

            start = perf_counter()
            baseline_rs = self._run_legacy_baseline(cond, updates, symbol_table)
            baseline_time = perf_counter() - start
            timings.append(
                (
                    formula_text,
                    len(generate_rs),
                    len(baseline_rs),
                    generate_time,
                    baseline_time,
                )
            )

            generate_formula = self._combos_to_formula(
                [x for x in generate_rs if x is not None]
            )
            baseline_formula = self._combos_to_formula(
                [x for x in baseline_rs if x is not None]
            )
            self.assertTrue(
                is_tautology(iff(generate_formula, baseline_formula), symbol_table),
                msg=(
                    "generate vs baseline mismatch\n"
                    f"formula: {formula_text}\n"
                    f"generate: {generate_formula}\n"
                    f"baseline: {baseline_formula}"
                ),
            )

        print("\nUpdate combination timings:")
        for (
            formula_text,
            generate_count,
            baseline_count,
            generate_time,
            baseline_time,
        ) in timings:
            ratio = baseline_time / generate_time if generate_time > 0 else float("inf")
            print(
                f"  formula={formula_text} | generate_count={generate_count} "
                f"| baseline_count={baseline_count} | generate={generate_time:.6f}s "
                f"| baseline={baseline_time:.6f}s | baseline/generate={ratio:.3f}"
            )


if __name__ == "__main__":
    unittest.main()
