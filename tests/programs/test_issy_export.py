import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from unittest import TestCase

from programs.issy_export import IssyPrinter, issy_names, program_to_issy
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import BOOLEAN, INTEGER, NATURAL, parse_type
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import true, false
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestIssyExport(TestCase):
    def assert_compiles(self, text):
        """Set ISSY_BINARY to enable validation with Issy v3's compiler."""
        compiler = os.environ.get("ISSY_BINARY")
        if compiler:
            result = subprocess.run(
                [compiler, "--compile", "-"],
                input=text, capture_output=True, text=True, timeout=10,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertNotIn("Compiler error", result.stderr + result.stdout)
            return result.stdout

    def setUp(self):
        self.x = Variable("x")
        self.cx = Variable("cx")
        self.printer = IssyPrinter({"x": INTEGER, "cx": BOOLEAN})

    def test_formulas_and_bracketed_arithmetic(self):
        predicate = BiOp(BiOp(self.x, "+", Value(1)), "<=", Value(50))
        formula = BiOp(UniOp("G", self.cx), "&", UniOp("F", MathExpr(predicate)))
        self.assertEqual(
            self.printer.formula(formula),
            "(G([cx]) && F([(x + 1) <= 50]))",
        )
        self.assertEqual(self.printer.formula(true()), "true")
        self.assertEqual(self.printer.formula(false()), "false")
        self.assertEqual(
            self.printer.formula(BiOp(self.x, "!=", Value(0))), "!([x = 0])"
        )
        self.assertEqual(
            self.printer.formula(BiOp(self.cx, "|", false())), "([cx] || false)"
        )

    def test_boolean_initial_values_and_updates(self):
        self.assertEqual(
            self.printer.formula(Update(self.cx, true())), "[cx']"
        )
        self.assertEqual(
            self.printer.formula(Update(self.cx, false())), "![cx']"
        )
        self.assertEqual(
            self.printer.formula(BiOp(self.cx, "=", false())), "![cx]"
        )

        for value, expected in ((true(), "cx~"), (false(), "(not cx~)")):
            with self.subTest(value=str(value)):
                atom = self.printer.formula(Update(self.cx, value))
                compiled = self.assert_compiles(
                    "state bool cx\ngame Safety from q0 {\nloc q0 1\n"
                    f"from q0 to q0 with {atom}\n}}"
                )
                if compiled is not None:
                    self.assertIn(f"(q0 q0 {expected})", compiled)

    def test_boolean_equivalence_avoids_issy_compiler_bug(self):
        other = Variable("other")
        printer = IssyPrinter({"cx": BOOLEAN, "other": BOOLEAN})
        for operator in ("=", "!=", "<->"):
            with self.subTest(operator=operator):
                text = printer.formula(BiOp(self.cx, operator, other))
                self.assertNotIn("<->", text)
                compiled = self.assert_compiles(
                    "state bool cx\nstate bool other\n"
                    "game Safety from q0 {\nloc q0 1\n"
                    f"from q0 to q0 with {text}\n}}"
                )
                if compiled is not None:
                    self.assertIn(
                        "(or (and cx other) (and (not cx) (not other)))", compiled
                    )
                    if operator == "!=":
                        self.assertIn("(not (or", compiled)

    def test_parallel_transitions_keep_guard_update_pairs(self):
        flag = Variable("flag")
        program = SimpleNamespace(
            states={"q1", "q0"}, initial_state="q0",
            symbol_table={"x": INTEGER, "cx": BOOLEAN, "flag": BOOLEAN},
            env_events=[], con_events=[("cx", BOOLEAN)], local_vars=[self.x, flag],
            init_var_values={"x": Value(0), "flag": true()},
            transitions=[
                Transition(
                    "q0", true(),
                    [Update(self.x, Value(0)), Update(flag, false())],
                    [], "q1",
                ),
                Transition("q1", self.cx, [Update(self.x, BiOp(self.x, "+", Value(1)))], [], "q1"),
                Transition("q1", UniOp("!", self.cx), [Update(self.x, self.x)], [], "q1"),
            ],
        )
        text = program_to_issy(program, UniOp("G", Variable("q1")))
        self.assertEqual(text.count("from q1 to q1 with"), 1)
        self.assertIn("([cx'] && [x' = (x + 1)] && [q1'])", text)
        self.assertIn("(!([cx']) && keep(x) && [q1'])", text)
        self.assertIn(" || ", text)
        self.assertIn("assume ![q1]", text)
        self.assertIn("state bool q1", text)
        self.assertIn("assume [flag] && [x = 0]", text)
        self.assertIn("![flag']", text)
        self.assert_compiles(text)
        program.transitions.reverse()
        self.assertEqual(text, program_to_issy(program, UniOp("G", Variable("q1"))))

    def test_gf_real_program(self):
        from parsing.string_to_program import string_to_program

        root = Path(__file__).resolve().parents[2]
        path = root / "benchmarks/sweap/non-det-inputs/popl25/basic/gf-real.prog"
        program, spec = string_to_program(path.read_text())
        text = program.to_issy(spec)
        self.assertIn("assert (X(G([cx'])) && G(F([x > 1000])))", text)
        self.assertEqual(text.count("from q1 to q1 with"), 1)
        self.assertNotIn("TRUE", text)
        self.assertNotIn(" & ", text)
        self.assertNotIn(" | ", text)
        self.assert_compiles(text)

    def test_controller_references_are_primed_in_guards_updates_and_ltl(self):
        event, flag = Variable("event"), Variable("flag")
        program = SimpleNamespace(
            states={"q0"}, initial_state="q0",
            symbol_table={"cx": BOOLEAN, "event": BOOLEAN, "flag": BOOLEAN},
            env_events=[(event, BOOLEAN)], con_events=[(self.cx, BOOLEAN)],
            local_vars=[flag], init_var_values={"flag": false()},
            transitions=[Transition(
                "q0", BiOp(event, "&", self.cx), [Update(flag, self.cx)], [], "q0"
            )],
        )
        objective = BiOp(
            UniOp("G", BiOp(event, "->", self.cx)), "&",
            BiOp(UniOp("X", self.cx), "&", flag),
        )
        text = program_to_issy(program, objective)
        self.assertIn("state bool cx\n", text)
        self.assertNotIn("state bool cx'", text)
        self.assertIn("G(([event] -> [cx']))", text)
        self.assertIn("X([cx'])", text)
        self.assertIn("&& [flag])", text)
        self.assertIn("([event] && [cx'])", text)
        self.assertIn("([flag'] && [cx'])", text)
        self.assertNotIn("[cx]", text)
        self.assertNotIn("cx''", text)
        self.assert_compiles(text)
        self.assertIn("cx", str(objective))
        self.assertNotIn("cx'", str(objective))

    def test_controller_priming_preserves_renaming_and_existing_primes(self):
        printer = IssyPrinter({"keep": BOOLEAN}, controller_props={"keep"})
        name = issy_names({"keep"})["keep"]
        self.assertEqual(printer.formula(Variable("keep")), f"[{name}']")
        self.assertEqual(printer.formula(Variable("keep'")), f"[{name}']")

    def test_identifier_renaming_is_consistent_and_collision_free(self):
        names = {"_x", "x-y", "keep", "q-0", "1", "sweap5f78"}
        mapped = issy_names(names)
        self.assertEqual(mapped, issy_names(set(reversed(sorted(names)))))
        self.assertEqual(len(set(mapped.values())), len(names))
        self.assertEqual(mapped["sweap5f78"], "sweap5f78")
        self.assertNotEqual(mapped["_x"], mapped["sweap5f78"])
        for name in mapped.values():
            self.assertRegex(name, r"^[A-Za-z][A-Za-z0-9_]*$")

        x, event, keep, collision = map(
            Variable, ("_x", "x-y", "keep", "sweap5f78")
        )
        program = SimpleNamespace(
            states={"q-0", "1"}, initial_state="q-0",
            symbol_table={
                "_x": INTEGER, "x-y": INTEGER, "keep": BOOLEAN,
                "q-0": BOOLEAN, "1": BOOLEAN, "sweap5f78": INTEGER,
            },
            env_events=[(event, INTEGER)], con_events=[(keep, BOOLEAN)],
            local_vars=[x, collision], init_var_values={"_x": Value(0)},
            transitions=[Transition(
                "q-0", keep,
                [Update(x, BiOp(event, "+", Value(1))), Update(collision, collision)],
                [], "1",
            )],
        )
        text = program_to_issy(program, UniOp("G", Variable("q-0")))
        self.assertIn(f"input int {mapped['x-y']}", text)
        self.assertIn(f"state bool {mapped['keep']}", text)
        self.assertIn(f"assume [{mapped['_x']} = 0]", text)
        self.assertIn(f"assert G([{mapped['q-0']}])", text)
        self.assertIn(f"game Safety from {mapped['q-0']}", text)
        self.assertIn(f"from {mapped['q-0']} to {mapped['1']}", text)
        self.assertIn(f"[{mapped['_x']}' = ({mapped['x-y']} + 1)]", text)
        self.assertIn(f"![{mapped['q-0']}']", text)
        self.assertIn("keep(sweap5f78)", text)
        self.assert_compiles(text)

    def test_nondeterministic_updates_leave_other_updates_intact(self):
        x, y, flag = map(Variable, ("x", "y", "flag"))
        program = SimpleNamespace(
            states={"q0"}, initial_state="q0",
            symbol_table={"x": NATURAL, "y": INTEGER, "flag": BOOLEAN},
            env_events=[], con_events=[], local_vars=[x, y, flag],
            init_var_values={"x": Value(0), "y": Value(0), "flag": false()},
            transitions=[Transition(
                "q0", true(),
                [Update(x, NonDeterministic()), Update(flag, NonDeterministic()),
                 Update(y, BiOp(y, "+", Value(1)))],
                [], "q0",
            )],
        )
        text = program_to_issy(program, UniOp("G", BiOp(y, ">=", Value(0))))
        edge = next(line for line in text.splitlines() if "from q0 to q0 with" in line)
        self.assertIn("[x' >= 0]", edge)
        self.assertIn("[y' = (y + 1)]", edge)
        self.assertNotIn("flag'", edge)
        self.assertNotIn("keep(", edge)
        self.assertNotIn("havoc(", edge)
        self.assert_compiles(text)

    def test_nondeterministic_value_preserves_declared_bounds(self):
        for interval, lower, upper in (
            ("[-2..5]", ">=", "<="),
            ("[-2..5)", ">=", "<"),
            ("(-2..5]", ">", "<="),
            ("(-2..5)", ">", "<"),
        ):
            with self.subTest(interval=interval):
                printer = IssyPrinter({"x": parse_type(interval)})
                text = printer.formula(Update(self.x, NonDeterministic()))
                self.assertEqual(
                    text, f"([x' {lower} -2] && [x' {upper} 5])"
                )
                self.assertEqual(
                    printer.nondeterministic_value(self.x),
                    f"([x {lower} -2] && [x {upper} 5])",
                )
        self.assertEqual(
            self.printer.formula(Update(self.x, NonDeterministic())), "true"
        )

    def test_program_with_nondeterministic_assignment(self):
        from programs.program import Program

        program = Program(
            "nondeterministic_update", {"q0"}, "q0",
            [("x", NATURAL, Value(0))],
            [Transition(
                "q0", true(), [Update(self.x, NonDeterministic())], [], "q0"
            )],
            [], [], preprocess=False, is_determ=True,
        )
        text = program.to_issy(UniOp("G", BiOp(self.x, ">=", Value(0))))
        self.assertIn("[x' >= 0]", text)
        self.assert_compiles(text)

    def test_export_normalizes_temporal_operators(self):
        a, b = Variable("a"), Variable("b")
        program = SimpleNamespace(
            states={"q0"}, initial_state="q0",
            symbol_table={"a": BOOLEAN, "b": BOOLEAN}, env_events=[],
            con_events=[(a, BOOLEAN), (b, BOOLEAN)], local_vars=[],
            init_var_values={},
            transitions=[Transition("q0", true(), [], [], "q0")],
        )
        for op in ("W", "R", "M"):
            with self.subTest(operator=op):
                spec = BiOp(a, op, b)
                text = program_to_issy(program, spec)
                self.assertNotIn(f" {op} ", text)
                self.assertIn(" U ", text)
                self.assertEqual(str(spec.op), op)
                self.assert_compiles(text)

    def test_projected_constants_are_substituted_in_specification(self):
        from parsing.string_to_program import string_to_program

        program, spec = string_to_program("""
            program constant_demo {
                STATES { q0: init }
                ENVIRONMENT EVENTS {}
                CONTROLLER EVENTS {}
                VALUATION { b: bool := true; }
                TRANSITIONS { q0 -> q0 [true $ b := b] }
                SPECIFICATION { G b }
            }
        """)
        self.assertIn(Variable("b"), program.constants)
        self.assertNotIn("b", program.symbol_table)
        # Parsing already substitutes constants; also exercise the exporter directly.
        spec = UniOp("G", Variable("b"))
        original_spec = str(spec)
        text = program.to_issy(spec)
        self.assertIn("assert G([0 = 0])", text)
        self.assertNotIn("[b]", text)
        self.assertEqual(str(spec), original_spec)
        self.assert_compiles(text)

    def test_logical_constants_are_valid_temporal_atoms(self):
        printer = IssyPrinter({}, logical_constants=True)
        self.assertEqual(printer.formula(UniOp("G", true())), "G([0 = 0])")
        self.assertEqual(printer.formula(UniOp("G", false())), "G([0 = 1])")
        self.assert_compiles(
            "formula { assert G([0 = 0]) }\n"
            "game Safety from q0 { loc q0 1 from q0 to q0 with true }"
        )

    def test_input_domains_are_global_assumptions(self):
        for typ, expected in (
            (NATURAL, "[i >= 0]"),
            (parse_type("[-2..5)"), "([i >= -2] && [i < 5])"),
            (parse_type("(-2..5]"), "([i > -2] && [i <= 5])"),
        ):
            with self.subTest(typ=str(typ)):
                i = Variable("i")
                program = SimpleNamespace(
                    states={"q0"}, initial_state="q0", symbol_table={"i": typ},
                    env_events=[(i, typ)], con_events=[], local_vars=[],
                    init_var_values={},
                    transitions=[Transition("q0", true(), [], [], "q0")],
                )
                text = program_to_issy(program, true())
                self.assertIn(f"assume G({expected})", text)
                self.assertIn("input int i", text)
                self.assert_compiles(text)

    def test_unbounded_inputs_do_not_gain_domain_assumptions(self):
        program = SimpleNamespace(
            states={"q0"}, initial_state="q0",
            symbol_table={"i": INTEGER, "b": BOOLEAN},
            env_events=[(Variable("i"), INTEGER), (Variable("b"), BOOLEAN)],
            con_events=[], local_vars=[], init_var_values={},
            transitions=[Transition("q0", true(), [], [], "q0")],
        )
        text = program_to_issy(program, true())
        self.assertNotIn("assume", text)
        self.assert_compiles(text)

    def test_local_domains_are_location_invariants(self):
        program = SimpleNamespace(
            states={"q0", "q1"}, initial_state="q0",
            symbol_table={"x": NATURAL, "y": parse_type("(-2..5]")},
            env_events=[], con_events=[], local_vars=[self.x, Variable("y")],
            init_var_values={}, transitions=[
                Transition("q0", true(), [], [], "q1"),
                Transition("q1", true(), [], [], "q1"),
            ],
        )
        text = program_to_issy(program, true())
        for location in ("q0", "q1"):
            self.assertIn(
                f"loc {location} 1 with ([x >= 0] && ([y > -2] && [y <= 5]))",
                text,
            )
        self.assertNotIn("assume", text)
        self.assert_compiles(text)
