import re
import unittest
from pathlib import Path
from unittest.mock import patch

import parsec

import config
from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module
from prop_lang.nondet import NonDeterministic
from prop_lang.variable import Variable

REPO_ROOT = Path(__file__).resolve().parents[2]


def _build_stage1_game_programs(name, vars_or_macros, formula_objectives, games):
    dual = config.Config.getConfig().dual
    config.Config.getConfig().dual = False
    optimisation_summary = string_to_issy_module._new_optimisation_summary(name)
    try:
        problem_context = string_to_issy_module._prepare_context(
            vars_or_macros=vars_or_macros,
            formula_objectives=formula_objectives,
            optimisation_summary=optimisation_summary,
        )
        if len(games) == 0:
            (
                _con_vars,
                sub_programs,
                _states_to_exclude_minigame,
                _symbol_table,
                _declared_state_vars,
                _formula_objectives,
            ) = string_to_issy_module._process_formula_only_mode_stage1(
                name_str=name,
                problem_context=problem_context,
                optimisation_summary=optimisation_summary,
            )
        else:
            (
                sub_programs,
                _states_to_exclude_minigame,
                _con_vars,
                _symbol_table,
                _declared_state_vars,
                _formula_objectives,
            ) = string_to_issy_module._build_intermediate_game_program_data(
                name_str=name,
                games=games,
                problem_context=problem_context,
                optimisation_summary=optimisation_summary,
            )
        return [p for p, _, _ in sub_programs]
    finally:
        config.Config.getConfig().dual = dual


class _SequentialPool:
    def __init__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def map(self, fn, items):
        return [fn(item) for item in items]


class TestStringToIssyFormulaOnlyNondetUpdates(unittest.TestCase):
    def setUp(self):
        self._patchers = [
            patch.object(
                program_util_module,
                "run_with_timeout",
                lambda fn, args, timeout=0.2: (False, None),
            ),
        ]
        for p in self._patchers:
            p.start()

    def tearDown(self):
        for p in reversed(self._patchers):
            p.stop()

    def test_formula_only_unmentioned_state_var_is_explicitly_nondet_before_minigames(
        self,
    ):
        issy = """
        state int x
        state int y

        formula {
          assume [x = 0]
          assert G [x' = x + 1]
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        game_programs = _build_stage1_game_programs(
            "formula_only_nondet_pre_minigame.issy",
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertEqual(len(game_programs), 1)
        program = game_programs[0]

        # Formula-only exact transition encoding uses a single "eval" state.
        self.assertEqual(program.states, {"eval"})
        self.assertEqual(len(program.orig_ts), 1)
        transition = next(iter(program.orig_ts))
        updates = {str(a.left): a for a in transition.action}
        self.assertIn("x", updates)
        self.assertIn("y", updates)
        # Non-mentioned vars are explicitly nondeterministic before minigames.
        self.assertIsInstance(updates["y"].right, NonDeterministic)

    def test_formula_only_bool_nondet_uses_bool_event_without_minigame_state(self):
        issy = """
        state bool b

        formula {
          assert G [b]
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_bool_nondet.issy"
        )

        self.assertFalse(any("_minigame_" in s for s in program.states))
        self.assertEqual(set(program.states), {"eval", "lose"})
        self.assertTrue(
            any(
                str(v).startswith("minigame_bool_event_") for v, _ in program.con_events
            )
        )

        eval_transitions = [
            t for t in program.orig_ts if t.src == "eval" and t.tgt == "eval"
        ]
        self.assertEqual(len(eval_transitions), 1)
        updates = {str(a.left): a for a in eval_transitions[0].action}
        self.assertIn("b", updates)
        self.assertIsInstance(updates["b"].right, Variable)
        self.assertTrue(str(updates["b"].right).startswith("minigame_bool_event_"))

    def test_formula_only_constant_only_var_gets_constant_choice_minigame(self):
        issy = """
        state int y

        formula {
          assert G [y = 0]
        }
        """
        program, _objective = string_to_issy_module.string_to_issy(
            issy, "formula_only_const_choice.issy"
        )

        self.assertIn("y", program.local_vars_str)
        self.assertNotIn("int_y", program.local_vars_str)
        self.assertTrue(any("_minigame_" in s for s in program.states))

        set_y_zero = False
        set_y_other = False
        for t in program.orig_ts:
            for a in t.action:
                if str(a.left) != "y":
                    continue
                if str(a.right) == "0":
                    set_y_zero = True
                elif str(a.right) != "y":
                    set_y_other = True
        self.assertTrue(set_y_zero)
        self.assertTrue(set_y_other)

    def test_games_bool_state_promotion_updates_context_before_program_build(self):
        issy = """
        state bool q0

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with q0'
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        game_programs = _build_stage1_game_programs(
            "games_bool_state_promotion.issy",
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertEqual(len(game_programs), 1)
        game_program = game_programs[0]

        self.assertNotIn("q0", game_program.local_vars_str)
        self.assertIn("q0", {str(v) for v, _ in game_program.con_events})
        self.assertFalse(
            any(str(a.left) == "q0" for t in game_program.orig_ts for a in t.action)
        )

        final_program, _ = string_to_issy_module.process(
            "games_bool_state_promotion.issy",
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertNotIn("q0", final_program.local_vars_str)
        self.assertIn("q0", {str(v) for v, _ in final_program.con_events})

    def test_games_always_primed_bool_state_vars_become_controller_props(self):
        benchmark = REPO_ROOT / "benchmarks/issy/test-04-bool-version.issy"
        with benchmark.open() as handle:
            issy = handle.read()

        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        game_programs = _build_stage1_game_programs(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertTrue(len(game_programs) >= 1)
        for game_program in game_programs:
            self.assertIn("sched1", game_program.local_vars_str)
            self.assertIn("sched2", game_program.local_vars_str)
            con_event_names = {str(v) for v, _ in game_program.con_events}
            self.assertNotIn("sched1", con_event_names)
            self.assertNotIn("sched2", con_event_names)

        final_program, _ = string_to_issy_module.process(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertIn("sched1", final_program.local_vars_str)
        self.assertIn("sched2", final_program.local_vars_str)
        final_con_events = {str(v) for v, _ in final_program.con_events}
        self.assertNotIn("sched1", final_con_events)
        self.assertNotIn("sched2", final_con_events)

    def test_games_numeric_next_constant_state_var_is_preconverted_to_bool_props(self):
        benchmark = REPO_ROOT / "benchmarks/issy/test-04.issy"
        with benchmark.open() as handle:
            issy = handle.read()

        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        game_programs = _build_stage1_game_programs(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertTrue(len(game_programs) >= 1)
        for game_program in game_programs:
            self.assertNotIn("sched", game_program.local_vars_str)
            con_event_names = {str(v) for v, _ in game_program.con_events}
            self.assertIn("sched1", con_event_names)
            self.assertIn("sched2", con_event_names)
            self.assertTrue(
                any(
                    ("sched1" in str(t.condition)) or ("sched2" in str(t.condition))
                    for t in game_program.orig_ts
                )
            )

        final_program, final_objective = string_to_issy_module.process(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertNotIn("sched", final_program.local_vars_str)
        final_con_events = {str(v) for v, _ in final_program.con_events}
        self.assertIn("sched1", final_con_events)
        self.assertIn("sched2", final_con_events)
        self.assertNotIn("sched'", str(final_objective))

    def test_formula_only_numeric_constant_updates_promote_d_vars(self):
        benchmark = REPO_ROOT / "benchmarks/issy/formula-multiminigame-noexpgames1.issy"
        with benchmark.open() as handle:
            issy = handle.read()

        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        game_programs = _build_stage1_game_programs(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertTrue(len(game_programs) >= 1)
        for game_program in game_programs:
            self.assertNotIn("d0", game_program.local_vars_str)
            self.assertNotIn("d1", game_program.local_vars_str)

        stage1_con_event_names = {
            str(v) for p in game_programs for v, _ in p.con_events
        }
        self.assertTrue(any(name.startswith("d0") for name in stage1_con_event_names))
        self.assertTrue(any(name.startswith("d1") for name in stage1_con_event_names))

        final_program, final_objective = string_to_issy_module.process(
            benchmark.name,
            vars_or_macros,
            formula_objectives,
            games,
        )
        self.assertNotIn("d0", final_program.local_vars_str)
        self.assertNotIn("d1", final_program.local_vars_str)
        final_con_event_names = {str(v) for v, _ in final_program.con_events}
        self.assertTrue(any(name.startswith("d0") for name in final_con_event_names))
        self.assertTrue(any(name.startswith("d1") for name in final_con_event_names))
        self.assertNotIn("d0'", str(final_objective))
        self.assertNotIn("d1'", str(final_objective))

    def test_preconversion_supports_numeric_next_inequalities_in_counter_benchmark(
        self,
    ):
        benchmark = REPO_ROOT / "benchmarks/issy/counters/counter-10-10-game.issy"
        with benchmark.open() as handle:
            issy = handle.read()

        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            _,
            state_vars,
            _,
            raw_objectives,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        (
            rewritten_objectives,
            rewritten_games,
            promoted_con_props,
            _numeric_var_to_promoted_props,
            _standin_to_encoding,
            _standin_props,
            _promoted_bool_state_vars,
        ) = string_to_issy_module._promote_next_state_vars_to_controller_props(
            games,
            raw_objectives,
            state_vars,
            symbol_table,
        )

        self.assertIn(Variable("d1"), promoted_con_props)
        self.assertIn(Variable("d2"), promoted_con_props)
        self.assertIn(Variable("d3"), promoted_con_props)
        self.assertIn(Variable("d4"), promoted_con_props)
        self.assertNotIn(Variable("d"), state_vars)
        self.assertNotIn("d", symbol_table)
        self.assertNotIn("d'", symbol_table)
        self.assertEqual(len(rewritten_objectives), len(raw_objectives))

        for _game_type, _init, _locs, transitions in rewritten_games:
            for _src, f, _tgt in transitions:
                for v in f.variablesin():
                    if isinstance(v, Variable):
                        base = v.prev_rep().name if v.is_next() else v.name
                        self.assertNotEqual(base, "d")

    def test_preconversion_supports_strict_and_non_strict_next_inequalities(self):
        issy = """
        state int d

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with ([d' > 1] || [d' < -1] || [d' <= 3] || [d' >= -2] || [d' = 0])
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            _,
            state_vars,
            _,
            raw_objectives,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        (
            _rewritten_objectives,
            rewritten_games,
            promoted_con_props,
            _numeric_var_to_promoted_props,
            _standin_to_encoding,
            _standin_props,
            _promoted_bool_state_vars,
        ) = string_to_issy_module._promote_next_state_vars_to_controller_props(
            games,
            raw_objectives,
            state_vars,
            symbol_table,
        )

        self.assertTrue(len(promoted_con_props) > 0)
        self.assertNotIn(Variable("d"), state_vars)
        self.assertNotIn("d", symbol_table)
        self.assertNotIn("d'", symbol_table)

        for _game_type, _init, _locs, transitions in rewritten_games:
            for _src, f, _tgt in transitions:
                for v in f.variablesin():
                    if isinstance(v, Variable):
                        base = v.prev_rep().name if v.is_next() else v.name
                        self.assertNotEqual(base, "d")

    def test_guard_only_disjunction_does_not_force_update_combination_expansion(self):
        issy = """
        state int x
        input bool a

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with ([x' = 0] && (a || !a))
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            inputs,
            _,
            _,
            _,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        transition_formula = games[0][3][0][1]

        transitions = string_to_issy_module.formula_to_transitions(
            transition_formula,
            set(inputs),
            symbol_table,
        )
        self.assertTrue(len(transitions) >= 1)
        self.assertTrue(any(str(cond) == "(a | !a)" for cond, _ in transitions))

    def test_non_equality_update_disjunction_does_not_use_exhaustive_combinations(self):
        issy = """
        state int x

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with ([x' >= 0] || [x' <= 1])
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            inputs,
            _,
            _,
            _,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        transition_formula = games[0][3][0][1]

        transitions = string_to_issy_module.formula_to_transitions(
            transition_formula,
            set(inputs),
            symbol_table,
        )
        self.assertTrue(len(transitions) >= 1)
        self.assertTrue(all(str(cond) == "TRUE" for cond, _ in transitions))

    def test_top_level_guard_conjunct_is_factored_out_before_disjunct_analysis(self):
        issy = """
        state int x
        input bool a

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with (a && [x' = 0])
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            inputs,
            _,
            _,
            _,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        transition_formula = games[0][3][0][1]
        transitions = string_to_issy_module.formula_to_transitions(
            transition_formula,
            set(inputs),
            symbol_table,
        )

        self.assertTrue(len(transitions) >= 1)
        self.assertTrue(all(str(cond) == "a" for cond, _ in transitions))
        self.assertTrue(
            any(
                "x'" in str(u)
                for _, upds in transitions
                for group in upds
                for u in (group if isinstance(group, (set, frozenset)) else [group])
            )
        )

    def test_top_level_disjunction_is_processed_branchwise(self):
        issy = """
        state int x
        input bool a

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with ((a && [x' = 0]) || (!a && [x' = 1]))
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            inputs,
            _,
            _,
            _,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        transition_formula = games[0][3][0][1]
        transitions = string_to_issy_module.formula_to_transitions(
            transition_formula,
            set(inputs),
            symbol_table,
        )

        conds = {str(cond) for cond, _ in transitions}
        self.assertIn("a", conds)
        self.assertIn("!a", conds)
        self.assertGreaterEqual(len(transitions), 2)

    def test_compositional_conjunct_processing_splits_next_conjuncts(self):
        issy = """
        state int x
        state int y
        input bool a

        game Safety from l0 {
          loc l0 1
          from l0 to l0 with (a && ([x' = 0] || [x' = 1]) && ([y' = 0] || [y' = 1]))
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        (
            inputs,
            _,
            _,
            _,
            symbol_table,
        ) = string_to_issy_module._build_process_context(
            vars_or_macros, formula_objectives
        )

        transition_formula = games[0][3][0][1]
        transitions = string_to_issy_module.formula_to_transitions(
            transition_formula,
            set(inputs),
            symbol_table,
        )

        self.assertGreaterEqual(len(transitions), 4)
        for cond, update_groups in transitions:
            self.assertIn("a", str(cond))
            self.assertEqual(len(update_groups), 1)
            updates = next(iter(update_groups))
            update_terms = {str(u) for u in updates}
            self.assertTrue(any("x'" in u for u in update_terms))
            self.assertTrue(any("y'" in u for u in update_terms))


if __name__ == "__main__":
    unittest.main()
