import re
import unittest
from unittest.mock import patch

import parsec

from parsing import string_to_issy as string_to_issy_module
from programs import util as program_util_module
from prop_lang.nondet import NonDeterministic


class TestStringToIssyMissingStateNondetUpdates(unittest.TestCase):
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

    def test_missing_declared_state_var_gets_nondet_action_after_cross_product(self):
        issy = """
        state int x
        state int y

        game Safety from l0 {
            loc l0 1
            from l0 to l0 with [x' = x + 1]
        }
        """
        input_wo_comments = re.sub("//.*(\\n|$)", "", issy).strip()
        vars_or_macros, formula_objectives, games = (
            string_to_issy_module.parser << parsec.eof()
        ).parse(input_wo_comments)

        problem_context = string_to_issy_module._prepare_context(
            vars_or_macros=vars_or_macros,
            formula_objectives=formula_objectives,
            optimisation_summary={},
        )
        (
            sub_programs,
            states_to_exclude_minigame,
            con_vars,
            symbol_table,
            declared_state_vars,
            _normalized_formula_objectives,
        ) = string_to_issy_module._build_intermediate_game_program_data(
            "missing_state_var_cross_product",
            games,
            problem_context,
        )

        (
            pre_program,
            _game_objectives,
            _to_exclude_from_minigame,
            _lose_var,
        ) = string_to_issy_module._cross_product_intermediate_programs(
            "missing_state_var_cross_product",
            sub_programs,
            states_to_exclude_minigame,
            con_vars,
            symbol_table,
            declared_state_vars,
        )

        self.assertIn("y", pre_program.local_vars_str)

        base_transitions = list(pre_program.orig_ts)
        self.assertGreater(len(base_transitions), 0)
        for t in base_transitions:
            y_updates = [a for a in t.action if str(a.left) == "y"]
            self.assertEqual(len(y_updates), 1)
            self.assertIsInstance(y_updates[0].right, NonDeterministic)


if __name__ == "__main__":
    unittest.main()
