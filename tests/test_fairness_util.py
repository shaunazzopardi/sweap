import os
import shutil
from unittest import TestCase
from unittest.mock import patch

from analysis.ranker import Ranker, cpa_path
from analysis.refinement.fairness_refinement.fairness_util import (
    function_has_well_ordered_range,
    function_decreases_in_loop_body,
    try_liveness_refinement,
)
from analysis.refinement.fairness_refinement.ranking_refinement import loop_to_c
from config import Config
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.types.types import NATURAL, INTEGER, BOOLEAN
from prop_lang.biop import BiOp
from prop_lang.update import Update
from prop_lang.util import conjunct, neg, sat
from prop_lang.value import Value
from prop_lang.variable import Variable
from programs.transition import Transition


class Test(TestCase):
    @staticmethod
    def _java_available():
        java = os.environ.get("JAVA")
        if java:
            return os.path.exists(java) or shutil.which(java) is not None
        return shutil.which("java") is not None

    def test_function_has_well_ordered_range(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        formula = Variable("x")

        result = function_has_well_ordered_range(formula, [], symbol_table)
        self.assertTrue(result)

    def test_function_decreases_in_loop_body(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "+", Value(1)))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(not result)

    def test_function_decreases_in_loop_body1(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "-", Value(1)))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)

    def test_function_decreases_in_loop_body2(self):
        symbol_table = {"x": NATURAL}
        symbol_table |= {"x_prev": NATURAL}
        x = Variable("x")
        body = [[Update(x, BiOp(x, "-", x))]]

        result = function_decreases_in_loop_body(x, [], body, symbol_table)

        self.assertTrue(result)

    class _DummyPredicateAbstraction:
        @staticmethod
        def get_symbol_table():
            return {}

    def test_skips_liveness_refinement_when_all_mismatch_preds_are_prev(self):
        conf = Config.getConfig()
        old_only_safety = conf.only_safety
        conf.only_safety = False

        try:
            with patch(
                "analysis.refinement.fairness_refinement.fairness_util.use_fairness_refinement"
            ) as fairness_check, patch(
                "analysis.refinement.fairness_refinement.fairness_util.liveness_step"
            ) as liveness_step:
                success, result = try_liveness_refinement(
                    Cs=None,
                    program=None,
                    predicate_abstraction=self._DummyPredicateAbstraction(),
                    agreed_on_execution=[],
                    disagreed_on_state=([string_to_prop("x_prev < x")], None),
                    signatures={},
                    loop_counter=0,
                    allow_user_input=False,
                )

            self.assertFalse(success)
            self.assertIsNone(result)
            fairness_check.assert_not_called()
            liveness_step.assert_not_called()
        finally:
            conf.only_safety = old_only_safety

    def test_filters_prev_preds_before_fairness_check(self):
        conf = Config.getConfig()
        old_only_safety = conf.only_safety
        conf.only_safety = False

        prev_pred = string_to_prop("x_prev < x")
        non_prev_pred = string_to_prop("x < 10")
        disagreed_on_state = ([prev_pred, non_prev_pred], "meta")

        try:
            with patch(
                "analysis.refinement.fairness_refinement.fairness_util.use_fairness_refinement"
            ) as fairness_check, patch(
                "analysis.refinement.fairness_refinement.fairness_util.liveness_step"
            ) as liveness_step:
                fairness_check.return_value = (False, None, None, None, None)

                success, result = try_liveness_refinement(
                    Cs=None,
                    program=None,
                    predicate_abstraction=self._DummyPredicateAbstraction(),
                    agreed_on_execution=[],
                    disagreed_on_state=disagreed_on_state,
                    signatures={},
                    loop_counter=0,
                    allow_user_input=False,
                )

            self.assertFalse(success)
            self.assertIsNone(result)
            fairness_check.assert_called_once()
            passed_disagreed_on_state = fairness_check.call_args.args[3]
            self.assertEqual(
                [str(non_prev_pred)], [str(p) for p in passed_disagreed_on_state[0]]
            )
            self.assertEqual(disagreed_on_state[1], passed_disagreed_on_state[1])
            liveness_step.assert_not_called()
        finally:
            conf.only_safety = old_only_safety

    def test_loop_to_c_only_snapshots_vars_updated_nontrivially(self):
        x = Variable("x")
        dx = Variable("dx")
        tx = Variable("tx")
        target = Variable("target")
        symbol_table = {
            "x": INTEGER,
            "dx": INTEGER,
            "tx": INTEGER,
            "target": INTEGER,
        }
        transition = Transition(
            "q0",
            string_to_prop("TRUE"),
            [
                Update(dx, dx),
                Update(tx, target),
                Update(x, BiOp(x, "+", dx)),
                Update(target, target),
            ],
            [],
            "q0",
        )

        class _DummyProgram:
            local_vars = [x, dx, tx, target]
            num_in_out = []

        c_code = loop_to_c(
            symbol_table,
            _DummyProgram(),
            string_to_prop("TRUE"),
            [transition],
            string_to_prop("x < 0"),
        )

        self.assertIn("x_prev = x;", c_code)
        self.assertIn("tx = target;", c_code)
        self.assertIn("x = (x_prev + dx);", c_code)
        self.assertNotIn("tx = target_prev;", c_code)
        self.assertNotIn("x = (x_prev + dx_prev);", c_code)

    def test_loop_to_c_matches_robot_error_log_transition_list(self):
        x = Variable("x")
        dx = Variable("dx")
        tx = Variable("tx")
        target = Variable("target")
        ed1 = Variable("ed1")
        d1 = Variable("d1")
        d2 = Variable("d2")
        ct = Variable("ct")
        cx = Variable("cx")

        symbol_table = {
            "x": INTEGER,
            "dx": INTEGER,
            "tx": INTEGER,
            "target": INTEGER,
            "ed1": BOOLEAN,
            "d1": BOOLEAN,
            "d2": BOOLEAN,
            "ct": BOOLEAN,
            "cx": BOOLEAN,
        }
        body = [
            Transition(
                "setTarget",
                string_to_prop("ed1"),
                [
                    Update(target, Value(1000)),
                    Update(x, x),
                    Update(dx, dx),
                    Update(tx, tx),
                ],
                [],
                "q",
            ),
            Transition(
                "q",
                string_to_prop("!d1 & !d2 & ct & cx"),
                [
                    Update(dx, dx),
                    Update(tx, target),
                    Update(x, BiOp(x, "+", dx)),
                    Update(target, target),
                ],
                [],
                "setTarget",
            ),
        ]

        class _DummyProgram:
            local_vars = [x, dx, tx, target]
            num_in_out = [ed1, d1, d2, ct, cx]

        c_code = loop_to_c(
            symbol_table,
            _DummyProgram(),
            string_to_prop("TRUE"),
            body,
            string_to_prop(
                "!((x + -tx) <= -1) & ((x + -tx) <= 0) & !(tx <= -1000) & (tx <= 999)"
            ),
        )

        self.assertIn("target = 1000;", c_code)
        self.assertIn("x_prev = x;", c_code)
        self.assertIn("tx = target;", c_code)
        self.assertIn("x = (x_prev + dx);", c_code)
        self.assertNotIn("target_prev = target;", c_code)
        self.assertNotIn("dx_prev = dx;", c_code)
        self.assertNotIn("tx = target_prev;", c_code)
        self.assertNotIn("x = (x_prev + dx_prev);", c_code)

    def test_robot_error_log_loop_exits_after_one_iteration_under_logged_precondition(
        self,
    ):
        x = Variable("x")
        dx = Variable("dx")
        tx = Variable("tx")
        target = Variable("target")

        symbol_table = {
            "x": INTEGER,
            "dx": INTEGER,
            "tx": INTEGER,
            "target": INTEGER,
        }

        pre = string_to_prop(
            "!(tx <= -1000) & (tx <= 999) & !((x + -tx) <= -1) & ((x + -tx) <= 0) & (tx <= 1000)"
        )
        exit_cond = string_to_prop(
            "!(!(!(tx <= 999) & (tx <= 1000)) && !(tx <= -1000) && (tx <= 999) && !((x + -tx) <= -1) && !((x + -tx) <= -1) && ((x + -tx) <= 0))"
        )

        # This mirrors the fixed loop body from the error log:
        #   target := 1000;
        #   tx := target;
        #   x := x + dx;
        post_exit = exit_cond.replace_vars(
            {
                x: BiOp(x, "+", dx),
                tx: Value(1000),
                target: Value(1000),
            }
        ).simplify()

        self.assertFalse(sat(conjunct(pre, neg(post_exit)), symbol_table))

    def test_robot_error_log_loop_terminates_in_cpachecker(self):
        if not self._java_available():
            self.skipTest("Java 17+ is not available")

        if not os.path.exists(os.path.join(cpa_path, "cpa.sh")):
            self.skipTest("Bundled CPAchecker script is not available")

        x = Variable("x")
        dx = Variable("dx")
        tx = Variable("tx")
        target = Variable("target")
        ed1 = Variable("ed1")
        d1 = Variable("d1")
        d2 = Variable("d2")
        ct = Variable("ct")
        cx = Variable("cx")

        symbol_table = {
            "x": INTEGER,
            "dx": INTEGER,
            "tx": INTEGER,
            "target": INTEGER,
            "ed1": BOOLEAN,
            "d1": BOOLEAN,
            "d2": BOOLEAN,
            "ct": BOOLEAN,
            "cx": BOOLEAN,
        }
        body = [
            Transition(
                "setTarget",
                string_to_prop("ed1"),
                [
                    Update(target, Value(1000)),
                    Update(x, x),
                    Update(dx, dx),
                    Update(tx, tx),
                ],
                [],
                "q",
            ),
            Transition(
                "q",
                string_to_prop("!d1 & !d2 & ct & cx"),
                [
                    Update(dx, dx),
                    Update(tx, target),
                    Update(x, BiOp(x, "+", dx)),
                    Update(target, target),
                ],
                [],
                "setTarget",
            ),
        ]

        class _DummyProgram:
            local_vars = [x, dx, tx, target]
            num_in_out = [ed1, d1, d2, ct, cx]

        c_code = loop_to_c(
            symbol_table,
            _DummyProgram(),
            string_to_prop(
                "!(tx <= -1000) & (tx <= 999) & !((x + -tx) <= -1) & ((x + -tx) <= 0) & (tx <= 1000)"
            ),
            body,
            string_to_prop(
                "!(!(!(tx <= 999) & (tx <= 1000)) && !(tx <= -1000) && (tx <= 999) && !((x + -tx) <= -1) && !((x + -tx) <= -1) && ((x + -tx) <= 0))"
            ),
        )

        success, _ = Ranker().check(c_code)
        self.assertTrue(success)
