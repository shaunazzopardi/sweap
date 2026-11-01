from unittest import TestCase

from pysmt.shortcuts import Int, Symbol
from pysmt.typing import INT

from prop_lang.types.types import parse_type
from prop_lang.util import type_constraint
from prop_lang.variable import Variable


class TestTypeConstraintBounds(TestCase):
    def test_endpoint_inclusivity(self):
        for lower_closed in (False, True):
            for upper_closed in (False, True):
                interval = (
                    ("[" if lower_closed else "(") + "-2..5"
                    + ("]" if upper_closed else ")")
                )
                with self.subTest(interval=interval):
                    table = {"x": parse_type(interval)}
                    constraint, _ = type_constraint(Variable("x"), table).to_smt(table)
                    for value in (-3, -2, -1, 4, 5, 6):
                        expected = (
                            (value >= -2 if lower_closed else value > -2)
                            and (value <= 5 if upper_closed else value < 5)
                        )
                        actual = constraint.substitute(
                            {Symbol("x", INT): Int(value)}
                        ).simplify().is_true()
                        self.assertEqual(actual, expected, (interval, value))
