from unittest import TestCase
from unittest.mock import patch

from parsing.string_to_program import string_to_program, postprocess_complex_action_program
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.util import conjunct_formula_set, equivalent
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestRelationalActionPreprocessing(TestCase):
    def test_by_order_preserves_relational_increment(self):
        results = []
        for options in ("completion=stutter", "semantics=by-order, completion=stutter"):
            with self.subTest(options=options):
                program, spec = string_to_program(f"""
                    program ordered_relation {{
                        STATES {{ q : init }}
                        ENVIRONMENT EVENTS {{}}
                        CONTROLLER EVENTS {{}}
                        VALUATION {{ x : integer := 0; }}
                        TRANSITIONS [{options}] {{
                            q -> q [true # x' = x + 1]
                        }}
                        SPECIFICATION {{ G(x >= 0) }}
                    }}
                """)
                self.assertIn("x", program.symbol_table)
                self.assertIn(Variable("x"), spec.variablesin())
                updates = [u for t in program.orig_ts for u in t.action]
                self.assertEqual(len(updates), 1)
                self.assertEqual(updates[0].left, Variable("x"))
                self.assertEqual(
                    updates[0].right, BiOp(Variable("x"), "+", Value(1))
                )
                results.append((program.orig_ts, spec))
        self.assertEqual(results[0], results[1])

    def parse_and_capture(self, valuation, action):
        captured = []

        def postprocess(program, spec):
            captured.extend(p for t in program.orig_ts for p in t.pred_upgrades)
            return postprocess_complex_action_program(program, spec)

        text = f"""
        program relational_preprocessing {{
            STATES {{ q : init }}
            ENVIRONMENT EVENTS {{}}
            CONTROLLER EVENTS {{}}
            VALUATION {{ {valuation} }}
            TRANSITIONS [completion=stutter] {{ q -> q [true # {action}] }}
            SPECIFICATION {{ G true }}
        }}
        """
        with patch('parsing.string_to_program.postprocess_complex_action_program', postprocess):
            program, spec = string_to_program(text)
        return program, captured

    def test_type_guard_keeps_residual_relation(self):
        program, predicates = self.parse_and_capture(
            'x : integer; y : natural;', "(x' > x) & (y' = y - 1)"
        )
        self.assertTrue(predicates)
        self.assertTrue(equivalent(
            conjunct_formula_set(predicates), BiOp(Variable("x'"), '>', Variable('x')),
            {'x': INTEGER, "x'": INTEGER},
        ))
        self.assertTrue(any('minigame' in state for state in program.states))

    def test_projection_substitutes_current_and_next_constants(self):
        program, predicates = self.parse_and_capture(
            'x : integer := 0; y : integer;',
            "(x' = x) & (y' > x) & (y' > x')",
        )
        self.assertTrue(predicates)
        self.assertTrue(equivalent(
            conjunct_formula_set(predicates), BiOp(Variable("y'"), '>', Value(0)),
            {"y'": INTEGER},
        ))
        self.assertNotIn('x', program.symbol_table)
        # With a trivial objective, minigame optimisation may eliminate the game;
        # the captured relation above checks the constraint before optimisation.
