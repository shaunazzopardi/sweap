"""Check assignment bounds at both endpoints and on constant assignments."""

from itertools import product
from unittest import TestCase

import config
from analysis.compatibility_checking.program_to_nuxmv import create_nuxmv_model, program_to_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.string_to_program import string_to_program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.types.types import NATURAL, BaseNumberTypes, Interval, Number
from prop_lang.update import Update
from prop_lang.util import conjunct, conjunct_formula_set, sat, true, type_constraints_acts
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestBoundedUpdateGuards(TestCase):
    def test_all_endpoint_combinations_and_constant_updates(self):
        for lower_inclusive, upper_inclusive in product((False, True), repeat=2):
            name = f"bounded_{int(lower_inclusive)}_{int(upper_inclusive)}"
            x = Variable(name)
            typ = Number(BaseNumberTypes.integer, Interval(
                "0", "2", lower_inclusive, upper_inclusive
            ))
            symbols = {name: typ}
            in_domain = lambda value: (
                (value >= 0 if lower_inclusive else value > 0)
                and (value <= 2 if upper_inclusive else value < 2)
            )
            updates = [(BiOp(x, "+", Value(str(d))), lambda value, d=d: value + d)
                       for d in (-1, 1)]
            updates += [(Value(str(n)), lambda value, n=n: n) for n in (-1, 0, 1, 2, 3)]
            for rhs, expected_value in updates:
                transition = Transition("q", true(), [Update(x, rhs)], [], "q")
                constraints = type_constraints_acts(transition, symbols)
                guard = conjunct_formula_set(constraints)
                for value in range(3):
                    if not in_domain(value):
                        continue
                    with self.subTest(type=typ, rhs=rhs, value=value):
                        enabled = sat(conjunct(guard, BiOp(x, "=", Value(str(value)))), symbols)
                        self.assertEqual(in_domain(expected_value(value)), enabled)
                if isinstance(rhs, Value):
                    # Closed arithmetic should be folded, rather than becoming
                    # variable-free predicates in synthesis normalisation.
                    self.assertTrue(all(isinstance(c, Value) for c in constraints))

    def test_impossible_bound_is_not_discarded(self):
        x = Variable("counter_at_max")
        symbols = {str(x): Number(BaseNumberTypes.integer, Interval("0", "2"))}
        condition = BiOp(x, "=", Value("2"))
        transition = Transition("q", condition, [Update(x, BiOp(x, "+", Value("1")))], [], "q")
        constraints = type_constraints_acts(transition, symbols)
        self.assertTrue(constraints)
        self.assertFalse(sat(conjunct(condition, conjunct_formula_set(constraints)), symbols))

    def test_natural_constants_are_checked(self):
        x = Variable("natural_constant_target")
        symbols = {str(x): NATURAL}
        for value in (-1, 0, 1):
            with self.subTest(value=value):
                transition = Transition("q", true(), [Update(x, Value(str(value)))], [], "q")
                constraints = type_constraints_acts(transition, symbols)
                self.assertEqual(value >= 0, sat(conjunct_formula_set(constraints), symbols))
                if value >= 0:
                    self.assertEqual([], constraints)

    def test_out_of_bounds_updates_stutter_without_deadlocking(self):
        conf = config.Config.getConfig()
        self.addCleanup(setattr, conf, "workers", conf.workers)
        self.addCleanup(setattr, conf, "dual", conf.dual)
        conf.workers, conf.dual = 1, False
        for update in ("x = 2 $ x := x + 1", "true $ x := 3"):
            with self.subTest(update=update):
                program, _ = string_to_program(f"""
                program upper_guard {{
                    STATES {{ q: init }}
                    ENVIRONMENT EVENTS {{ }}
                    CONTROLLER EVENTS {{ }}
                    VALUATION {{ x: [0..2] := 2; }}
                    TRANSITIONS [completion=stutter] {{ q -> q [{update}] }}
                    SPECIFICATION {{ G(x = 2) }}
                }}
                """)
                model = create_nuxmv_model(program_to_nuxmv_model(program))
                checker = ModelChecker()
                valid, output = checker.invar_check(model, "F FALSE", None, True)
                self.assertFalse(valid, output)
                valid, output = checker.invar_check(model, "G(x = 2)", None, True)
                self.assertTrue(valid, output)
