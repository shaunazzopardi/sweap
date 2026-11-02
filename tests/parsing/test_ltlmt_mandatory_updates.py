from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest import TestCase

from config import Config
from parsing.string_to_ltl import string_to_ltlmt
from parsing.string_to_ltlmt import ToProgram
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from synthesis.synthesis import synthesize


class TestLtlmtMandatoryUpdates(TestCase):
    def setUp(self):
        conf = Config.getConfig()
        for name, value in (("workers", 1), ("dual", False), ("debug", False),
                            ("verify_controller", False), ("log", False)):
            self.addCleanup(setattr, conf, name, getattr(conf, name))
            setattr(conf, name, value)
        output = redirect_stdout(StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)

    def translate(self, source, declarations=None):
        formulas, parsed_declarations = string_to_ltlmt(source)
        program, objective = ToProgram().ltlmt2prog(
            formulas, name="mandatory_updates",
            var_decs=parsed_declarations if declarations is None else declarations,
        )
        self.assert_no_updates(objective)
        return program, objective

    def assert_no_updates(self, formula):
        self.assertNotIsInstance(formula, Update)
        if isinstance(formula, BiOp):
            self.assert_no_updates(formula.left)
            self.assert_no_updates(formula.right)
        elif isinstance(formula, UniOp):
            self.assert_no_updates(formula.right)
        elif isinstance(formula, MathExpr):
            self.assert_no_updates(formula.formula)

    def choices(self, program, variable):
        return {
            str(update.right)
            for transition in program.transitions if transition.src == "c_" + variable
            for update in transition.action if str(update.left) == variable
        }

    def test_single_required_update_removes_implicit_stutter(self):
        program, _ = self.translate("always guarantee { [x <- i1()]; }")
        self.assertEqual(self.choices(program, "x"), {"1"})

    def test_disjunction_keeps_all_allowed_updates(self):
        program, _ = self.translate("always guarantee { [x <- i1()] || [x <- i2()]; }")
        self.assertEqual(self.choices(program, "x"), {"1", "2"})

    def test_boolean_required_update(self):
        program, _ = self.translate("always guarantee { [b <- true]; }")
        self.assertEqual(self.choices(program, "b"), {"TRUE"})

    def test_explicit_stutter_remains(self):
        program, _ = self.translate("always guarantee { [x <- x] || [x <- i1()]; }")
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_conjoined_requirements_intersect(self):
        program, _ = self.translate("""always guarantee {
            ([x <- i1()] || [x <- i2()]) && ([x <- i2()] || [x <- i3()]);
        }""")
        self.assertEqual(self.choices(program, "x"), {"2"})

    def test_arithmetic_aliases_remain_allowed(self):
        program, _ = self.translate("""always guarantee {
            [x <- add x i1()] || [x <- i2()];
            [x <- add i1() x] || [x <- i2()];
        }""")
        choices = self.choices(program, "x")
        self.assertNotIn("x", choices)
        self.assertIn("2", choices)
        self.assertTrue(any("+" in choice for choice in choices))

    def test_repeated_terms_are_not_treated_as_update_aliases(self):
        program, objective = self.translate("""always guarantee {
            [x <- add y y];
        }
        guarantee { F([x <- y]); }
        """)
        self.assertEqual(self.choices(program, "x"), {"(y + y)"})
        self.assertIn("FALSE", str(objective))

    def test_initial_state_and_temporal_input_assumptions_allow_pruning(self):
        program, _ = self.translate("""assume { eq x i0(); }
            always assume { eq i i0() || eq i i1(); }
            always guarantee { [x <- add x i]; }
        """)
        self.assertEqual(self.choices(program, "x"), {"(x + i)"})

    def test_conjoined_initial_and_temporal_input_assumptions_allow_pruning(self):
        program, _ = self.translate("""assume {
            eq x i0() && G(eq i i0() || eq i i1());
        }
        always guarantee { [x <- add x i]; }
        """)
        self.assertEqual(self.choices(program, "x"), {"(x + i)"})

    def test_conjoined_future_state_assumption_preserves_escape_choice(self):
        program, _ = self.translate("""assume { eq x i0() && F(eq x i1()); }
            always guarantee { [x <- i1()]; false; }
        """)
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_disjunctive_assumptions_are_not_split(self):
        program, _ = self.translate("""assume { eq x i0() || F(eq x i1()); }
            always guarantee { [x <- i1()]; }
        """)
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_future_state_assumption_preserves_escape_choice(self):
        program, _ = self.translate("""assume { eq x i0(); F(eq x i1()); }
            always guarantee { [x <- i1()]; false; }
        """)
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_assumption_about_initial_update_preserves_escape_choice(self):
        program, _ = self.translate("""assume { [x <- i1()]; }
            always guarantee { [x <- i2()]; false; }
        """)
        self.assertEqual(self.choices(program, "x"), {"x", "1", "2"})

    def test_conditional_guarantee_does_not_prune(self):
        program, _ = self.translate("always guarantee { p -> [x <- i1()]; }")
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_initial_update_requirement_does_not_prune_later_rounds(self):
        program, _ = self.translate("guarantee { [x <- i1()]; }")
        self.assertEqual(self.choices(program, "x"), {"x", "1"})

    def test_cross_variable_disjunction_does_not_prune(self):
        program, _ = self.translate("always guarantee { [x <- i1()] || [y <- i2()]; }")
        self.assertEqual(self.choices(program, "x"), {"x", "1"})
        self.assertEqual(self.choices(program, "y"), {"y", "2"})

    def test_constrained_types_keep_fallback_choices(self):
        for typ in ("Nat", "[0..2]"):
            with self.subTest(type=typ):
                program, _ = self.translate(
                    "always guarantee { [x <- sub x i1()]; }",
                    {"x": ("var", typ)},
                )
                self.assertIn("x", self.choices(program, "x"))

    def test_removed_update_references_become_false(self):
        program, objective = self.translate("""always guarantee { [x <- i1()]; }
            guarantee { F([x <- x]); }
        """)
        self.assertEqual(self.choices(program, "x"), {"1"})
        self.assertIn("FALSE", str(objective))
        self.assertFalse(synthesize(program, objective, None).realisable)

    def test_contradictory_requirements_stay_unrealisable(self):
        program, objective = self.translate("always guarantee { [x <- i1()]; [x <- i2()]; }")
        self.assertFalse(synthesize(program, objective, None).realisable)

    def test_assumption_falsification_still_synthesises(self):
        program, objective = self.translate("""assume { eq x i0(); F(eq x i1()); }
            always guarantee { [x <- i1()]; false; }
        """)
        self.assertTrue(synthesize(program, objective, None).realisable)

    def test_follow_keeps_only_required_environment_position_updates(self):
        path = Path(__file__).resolve().parents[2] / "benchmarks/raboniel/neider-follow.tslmt"
        program, _ = self.translate(path.read_text())
        self.assertEqual(len(program.transitions), 7)
        transitions = [t for t in program.transitions if t.src == "c_xe_ye"]
        self.assertEqual(len(transitions), 1)
        updates = {str(u.left): str(u.right) for u in transitions[0].action}
        self.assertEqual(updates["xe"], "(xe + env_x_move)")
        self.assertEqual(updates["ye"], "(ye + env_y_move)")
