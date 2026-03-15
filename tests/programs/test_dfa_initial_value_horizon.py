from unittest import TestCase
import random

from programs.dfa import (
    classify_initial_values,
    classify_initial_values_with_ltl_horizon,
)
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestInitialValueHorizon(TestCase):
    @staticmethod
    def _eq_zero(v: Variable):
        return BiOp(v, "=", Value("0"))

    def test_ignore_lose_state_can_recover_irrelevance(self):
        x = Variable("x")
        transitions = [
            Transition("s0", true(), [Update(x, Value("0"))], [], "s1"),
            Transition("s0", true(), [Update(x, x)], [], "lose"),
            Transition("s1", true(), [Update(x, x)], [], "s1"),
            Transition("lose", true(), [Update(x, x)], [], "lose"),
        ]
        program = Program(
            name="init_horizon_ignore_lose",
            sts=["s0", "s1", "lose"],
            init_st="s0",
            init_values=[("x", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp("X", self._eq_zero(x))

        relevant_all, irrelevant_all = classify_initial_values_with_ltl_horizon(
            program, objective, ignore_lose_state=False
        )
        self.assertIn(Variable("x"), relevant_all)
        self.assertNotIn(Variable("x"), irrelevant_all)

        relevant_nonlose, irrelevant_nonlose = (
            classify_initial_values_with_ltl_horizon(
                program, objective, ignore_lose_state=True
            )
        )
        self.assertNotIn(Variable("x"), relevant_nonlose)
        self.assertIn(Variable("x"), irrelevant_nonlose)

    def test_two_step_read_detects_post_overwrite_irrelevance(self):
        x = Variable("x")
        transitions = [
            Transition("s0", true(), [Update(x, x)], [], "s1"),
            Transition("s1", true(), [Update(x, Value("0"))], [], "s2"),
            Transition("s2", true(), [Update(x, x)], [], "s2"),
        ]
        program = Program(
            name="init_horizon_two_step",
            sts=["s0", "s1", "s2"],
            init_st="s0",
            init_values=[("x", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective_next = UniOp("X", self._eq_zero(x))
        relevant_next, irrelevant_next = classify_initial_values_with_ltl_horizon(
            program, objective_next
        )
        self.assertIn(Variable("x"), relevant_next)
        self.assertNotIn(Variable("x"), irrelevant_next)

        objective_next_next = UniOp("X", UniOp("X", self._eq_zero(x)))
        relevant_next_next, irrelevant_next_next = (
            classify_initial_values_with_ltl_horizon(program, objective_next_next)
        )
        self.assertNotIn(Variable("x"), relevant_next_next)
        self.assertIn(Variable("x"), irrelevant_next_next)

    def test_bad_state_cutoff_can_make_var_irrelevant(self):
        x = Variable("x")
        transitions = [
            Transition("s0", true(), [Update(x, x)], [], "bad"),
            Transition("bad", true(), [Update(x, x)], [], "s1"),
            Transition("s1", true(), [Update(x, x)], [], "s1"),
        ]
        program = Program(
            name="init_horizon_bad_cutoff",
            sts=["s0", "bad", "s1"],
            init_st="s0",
            init_values=[("x", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp("X", UniOp("X", self._eq_zero(x)))

        relevant_no_cutoff, _ = classify_initial_values_with_ltl_horizon(
            program, objective, bad_states=set()
        )
        self.assertIn(Variable("x"), relevant_no_cutoff)

        relevant_with_cutoff, irrelevant_with_cutoff = (
            classify_initial_values_with_ltl_horizon(
                program, objective, bad_states={"bad"}
            )
        )
        self.assertNotIn(Variable("x"), relevant_with_cutoff)
        self.assertIn(Variable("x"), irrelevant_with_cutoff)

    def test_bad_state_does_not_hide_pre_bad_guard_dependency(self):
        x = Variable("x")
        transitions = [
            Transition("s0", BiOp(x, "=", Value("0")), [Update(x, x)], [], "bad"),
            Transition("s0", true(), [Update(x, x)], [], "bad"),
            Transition("bad", true(), [Update(x, x)], [], "bad"),
        ]
        program = Program(
            name="init_horizon_bad_guard",
            sts=["s0", "bad"],
            init_st="s0",
            init_values=[("x", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp("X", self._eq_zero(x))
        relevant, irrelevant = classify_initial_values_with_ltl_horizon(
            program, objective, bad_states={"bad"}
        )
        self.assertIn(Variable("x"), relevant)
        self.assertNotIn(Variable("x"), irrelevant)

    def test_branching_non_overwrite_keeps_relevance(self):
        x = Variable("x")
        transitions = [
            Transition("s0", true(), [Update(x, Value("0"))], [], "s1"),
            Transition("s0", true(), [Update(x, x)], [], "s1"),
            Transition("s1", true(), [Update(x, x)], [], "s1"),
        ]
        program = Program(
            name="init_horizon_branching",
            sts=["s0", "s1"],
            init_st="s0",
            init_values=[("x", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp("X", self._eq_zero(x))
        relevant, irrelevant = classify_initial_values_with_ltl_horizon(program, objective)
        self.assertIn(Variable("x"), relevant)
        self.assertNotIn(Variable("x"), irrelevant)

    def test_taint_propagates_through_intermediate_variable(self):
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        transitions = [
            Transition(
                "s0",
                true(),
                [Update(y, x), Update(x, Value("0")), Update(z, z)],
                [],
                "s1",
            ),
            Transition("s1", true(), [Update(z, y), Update(x, x), Update(y, y)], [], "s2"),
            Transition("s2", true(), [Update(x, x), Update(y, y), Update(z, z)], [], "s2"),
        ]
        program = Program(
            name="init_horizon_taint_chain",
            sts=["s0", "s1", "s2"],
            init_st="s0",
            init_values=[("x", INTEGER), ("y", INTEGER), ("z", INTEGER)],
            transitions=transitions,
            env_events=[],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp("X", UniOp("X", self._eq_zero(z)))
        relevant, irrelevant = classify_initial_values_with_ltl_horizon(program, objective)
        self.assertIn(Variable("x"), relevant)
        self.assertNotIn(Variable("x"), irrelevant)

    def test_randomized_x_depth_stress_matches_reference_for_seed_x(self):
        def mk_obj(depth: int, target: Variable):
            f = BiOp(target, "=", Value("0"))
            for _ in range(depth):
                f = UniOp("X", f)
            return f

        def ref_may_matter(program: Program, depth: int, target: str, bad_states: set[str]):
            local_var_names = {v.name for v in program.local_vars}
            current = {(program.initial_state, frozenset({"x"}))}
            for step in range(depth + 1):
                if step == depth:
                    return any(target in tainted for _, tainted in current)
                next_configs = set()
                for state, tainted in current:
                    if str(state) in bad_states:
                        continue
                    outgoing = program.state_to_trans.get(state, [])
                    if len(outgoing) == 0:
                        next_configs.add((state, tainted))
                        continue
                    for t in outgoing:
                        if str(t.tgt) in bad_states:
                            continue
                        update_deps = {
                            str(u.left): {
                                str(v)
                                for v in u.right.variablesin()
                                if str(v) in local_var_names
                            }
                            for u in t.action
                            if str(u.left) in local_var_names
                        }
                        next_tainted = set()
                        for local_var_name in local_var_names:
                            rhs_vars = update_deps.get(local_var_name, {local_var_name})
                            if any(v in tainted for v in rhs_vars):
                                next_tainted.add(local_var_name)
                        next_configs.add((t.tgt, frozenset(next_tainted)))
                current = next_configs
                if len(current) == 0:
                    return False
            return False

        rng = random.Random(1237)
        x = Variable("x")
        y = Variable("y")
        for i in range(80):
            include_bad = (i % 4) == 0
            states = ["s0", "s1"] + (["bad"] if include_bad else [])
            transitions = []
            for s in states:
                if s == "bad":
                    transitions.append(
                        Transition(
                            "bad",
                            true(),
                            [Update(x, x), Update(y, y)],
                            [],
                            "bad",
                        )
                    )
                    continue
                for _ in range(rng.randint(1, 2)):
                    tgt = rng.choice(states)
                    choice_x = rng.choice(["self", "const", "other"])
                    choice_y = rng.choice(["self", "const", "other"])
                    rhs_x = (
                        x
                        if choice_x == "self"
                        else (Value("0") if choice_x == "const" else y)
                    )
                    rhs_y = (
                        y
                        if choice_y == "self"
                        else (Value("0") if choice_y == "const" else x)
                    )
                    transitions.append(
                        Transition(
                            s,
                            true(),
                            [Update(x, rhs_x), Update(y, rhs_y)],
                            [],
                            tgt,
                        )
                    )

            program = Program(
                name=f"init_horizon_rand_{i}",
                sts=states,
                init_st="s0",
                init_values=[("x", INTEGER), ("y", INTEGER)],
                transitions=transitions,
                env_events=[],
                con_events=[],
                preprocess=False,
                emit_state_binary_map=False,
            )

            depth = rng.randint(0, 4)
            target_name = rng.choice(["x", "y"])
            objective = mk_obj(depth, Variable(target_name))
            bad_states = {"bad"} if include_bad else set()

            relevant, _ = classify_initial_values_with_ltl_horizon(
                program,
                objective,
                bad_states=bad_states,
                ignore_lose_state=False,
            )
            observed = Variable("x") in relevant
            stage1_relevant, _ = classify_initial_values(program)
            if Variable("x") in stage1_relevant:
                expected = True
            else:
                expected = ref_may_matter(program, depth, target_name, bad_states)

            with self.subTest(i=i, depth=depth, target=target_name, states=states):
                self.assertEqual(observed, expected)
