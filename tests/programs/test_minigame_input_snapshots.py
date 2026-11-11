from unittest import TestCase
from unittest.mock import patch

from pysmt.shortcuts import Equals, Not, Solver

from programs.program import Program, fill_in_minigames
from programs import util as program_util_module
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.nondet import NonDeterministic
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestMinigameInputSnapshots(TestCase):
    def test_entry_bound_distinguishes_inputs_from_user_snapshot_named_locals(self):
        for existing_snapshot in (False, True):
            for relation, offset in ((">=", 0), ("<=", 0), (">", 1), ("<", -1)):
                with self.subTest(existing_snapshot=existing_snapshot, relation=relation):
                    x, inp, snapshot = map(Variable, ("x", "i", "curr_i"))
                    actions = [Update(x, NonDeterministic())]
                    initial = [("x", INTEGER, Value("0"))]
                    if existing_snapshot:
                        initial.append(("curr_i", INTEGER, Value("0")))
                        initial.append(("y", INTEGER, Value("0")))
                        actions.append(Update(snapshot, inp))
                        actions.append(Update(Variable("y"), snapshot))
                    transition = Transition("q", true(), actions, [], "q")
                    bound = BiOp(snapshot if existing_snapshot else inp, "+", Value("2"))
                    transition.set_predicate_upgrades([
                        BiOp(Variable("x'"), relation, bound),
                    ])
                    with patch.object(Program, "refine_var_types", lambda self: False), patch.object(
                        program_util_module, "run_with_timeout", lambda *args, **kwargs: (False, None)
                    ):
                        program = Program(
                            name="input_bound", sts=["q"], init_st="q", init_values=initial,
                            transitions=[transition], env_events=[(inp, INTEGER)], con_events=[],
                            preprocess=False, emit_state_binary_map=False,
                        )
                        result, minigames = fill_in_minigames(program, [BiOp(x, "<=", Value("0"))], [])
                    entries = [t for t in result.transitions if t.src == "q" and t.tgt in {str(v) for v in minigames}]
                    self.assertTrue(entries)
                    expected = BiOp(bound, "+", Value(str(offset)))
                    for entry in entries:
                        updates = {str(a.left): a.right for a in entry.action}
                        if existing_snapshot:
                            self.assertEqual(updates["curr_i"], inp)
                            self.assertEqual(updates["y"], snapshot)
                        else:
                            self.assertNotIn("curr_i", updates)
                        actual_smt = updates["x"].to_smt(result.symbol_table)[0]
                        expected_smt = expected.to_smt(result.symbol_table)[0]
                        # Universal equality: no assumption equates the old snapshot to i.
                        with Solver(name="z3") as solver:
                            solver.add_assertion(Not(Equals(actual_smt, expected_smt)))
                            self.assertFalse(solver.solve())

    def test_internal_stop_guard_reads_captured_input(self):
        x, z, inp = map(Variable, ("x", "z", "i"))
        transition = Transition(
            "q", true(), [Update(x, NonDeterministic()), Update(z, NonDeterministic()),
                          Update(Variable("curr_i"), Variable("curr_i"))],
            [], "q",
        )
        transition.set_predicate_upgrades([
            BiOp(Variable("x'"), ">=", inp),
            BiOp(Variable("z'"), "!=", inp),
        ])
        with patch.object(Program, "refine_var_types", lambda self: False), patch.object(
            program_util_module, "run_with_timeout", lambda *args, **kwargs: (False, None)
        ):
            program = Program(
                name="captured_stop", sts=["q"], init_st="q",
                init_values=[("x", INTEGER, Value("0")), ("z", INTEGER, Value("0")),
                             ("curr_i", INTEGER)],
                transitions=[transition], env_events=[(inp, INTEGER)], con_events=[],
                preprocess=False, emit_state_binary_map=False,
            )
            result, minigames = fill_in_minigames(program, [x, z, Variable("curr_i")], [])
        internal = [t for t in result.transitions if t.src in {str(v) for v in minigames}]
        self.assertTrue(internal)
        self.assertTrue(any(Variable("res_curr_i") in t.condition.variablesin() for t in internal))
        for transition in internal:
            self.assertNotIn(inp, transition.condition.variablesin())
            updates = {str(a.left): a.right for a in transition.action}
            self.assertEqual(updates["curr_i"], Variable("curr_i"))
            self.assertEqual(updates["res_curr_i"], Variable("res_curr_i"))
