"""Natural-number assignments must guard their result, not the old value."""

from unittest import TestCase

import config
from analysis.compatibility_checking.program_to_nuxmv import create_nuxmv_model, program_to_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.string_to_program import string_to_program
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER, NATURAL
from prop_lang.update import Update
from prop_lang.util import conjunct, next_type_constraint_from_act, neg, sat
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestNaturalUpdateGuards(TestCase):
    def test_decrement_requires_a_nonnegative_result(self):
        x = Variable("guarded_counter")
        symbols = {str(x): NATURAL}
        guard = next_type_constraint_from_act(
            Update(x, BiOp(x, "-", Value("1"))), symbols
        )
        self.assertFalse(sat(conjunct(guard, BiOp(x, "=", Value("0"))), symbols))
        self.assertTrue(sat(conjunct(guard, BiOp(x, "=", Value("1"))), symbols))

    def test_assignment_checks_the_rhs_variable(self):
        x, i = Variable("target_counter"), Variable("input_value")
        symbols = {str(x): NATURAL, str(i): INTEGER}
        guard = next_type_constraint_from_act(Update(x, i), symbols)
        self.assertFalse(sat(conjunct(guard, BiOp(i, "<", Value("0"))), symbols))
        self.assertTrue(sat(conjunct(guard, BiOp(i, "=", Value("0"))), symbols))

    def test_non_decreasing_update_needs_no_extra_guard(self):
        x = Variable("growing_counter")
        guard = next_type_constraint_from_act(
            Update(x, BiOp(x, "+", Value("1"))), {str(x): NATURAL}
        )
        self.assertTrue(guard.is_true())

    def test_invalid_decrement_is_covered_by_stutter(self):
        conf = config.Config.getConfig()
        previous_workers, previous_dual = conf.workers, conf.dual
        conf.workers, conf.dual = 1, False
        self.addCleanup(setattr, conf, "workers", previous_workers)
        self.addCleanup(setattr, conf, "dual", previous_dual)
        program, _ = string_to_program("""
        program natural_decrement {
            STATES { q: init }
            ENVIRONMENT EVENTS { }
            CONTROLLER EVENTS { decrement }
            VALUATION { x: natural := 0; }
            TRANSITIONS [completion=stutter] {
                q -> q [decrement $ x := x - 1],
                q -> q [!decrement $ x := x]
            }
            SPECIFICATION { G(x >= 0) }
        }
        """)
        x = Variable("x")
        decrement = next(t for t in program.orig_ts if t.action[0].right != x)
        zero = BiOp(x, "=", Value("0"))
        self.assertFalse(sat(conjunct(decrement.condition, zero), program.symbol_table))
        self.assertEqual(1, len(program.stutter_ts))
        stutter = program.stutter_ts[0]
        chosen = conjunct(zero, Variable("decrement"))
        self.assertFalse(sat(conjunct(chosen, neg(stutter.condition)), program.symbol_table))
        # Checking FALSE would pass vacuously if the requested decrement
        # deadlocked. There must be an infinite stuttering execution instead.
        model = create_nuxmv_model(program_to_nuxmv_model(program))
        model["main"] += "\nINVAR decrement\n"
        valid, output = ModelChecker().invar_check(model, "F FALSE", None, True)
        self.assertFalse(valid, output)
