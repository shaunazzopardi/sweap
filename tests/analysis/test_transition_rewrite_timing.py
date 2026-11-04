from types import SimpleNamespace
import pytest

from analysis.abstraction.effects_abstraction.to_ltl.one_trans_to_ltl import (
    to_ltl_organised_by_pred_effects_guard_updates,
)
from config import Config
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct
from prop_lang.variable import Variable


class TestTransitionRewriteTiming:
    @staticmethod
    def _next_depths(formula, depth=0, acc=None):
        if acc is None:
            acc = {}

        if isinstance(formula, Variable):
            acc.setdefault(str(formula), []).append(depth)
            return acc

        if isinstance(formula, UniOp):
            if formula.op == "X":
                return TestTransitionRewriteTiming._next_depths(
                    formula.right, depth + 1, acc
                )
            return TestTransitionRewriteTiming._next_depths(formula.right, depth, acc)

        if isinstance(formula, BiOp):
            TestTransitionRewriteTiming._next_depths(formula.left, depth, acc)
            TestTransitionRewriteTiming._next_depths(formula.right, depth, acc)

        return acc

    @pytest.mark.parametrize("dual", [False, True])
    def test_rewrite_shifts_props_to_expected_timesteps(self, dual, monkeypatch):
        request = Variable("request")
        grant_a = Variable("grantA")
        room_a = Variable("roomA")
        pred_room_a = Variable("pred_roomA")
        pred_effect = Variable("pred_eff")

        condition = conjunct(conjunct(request, grant_a), room_a)
        transition = Transition("q0", condition, [], [pred_room_a], "q1")

        program = SimpleNamespace(
            env_events=[(request, None)],
            con_events=[(grant_a, None)],
            bool_in_out=[request, grant_a],
            num_in_out=[],
            local_vars=[],
            symbol_table={},
            initial_state="q0",
            states_binary_map={
                "q0": Variable("source_state"),
                "q1": Variable("target_state"),
            },
        )

        abstraction = SimpleNamespace(
            program=program,
            init_state_abstraction=[[]],
            init_constants=[],
            gu_to_trans={condition: [transition]},
            var_relabellings={},
            abstract_effect_ltl={condition: pred_effect},
            init_program_trans=set(),
            non_init_program_trans={transition},
        )

        monkeypatch.setattr(Config.getConfig(), "dual", dual)
        _, constraints, _ = to_ltl_organised_by_pred_effects_guard_updates(
            abstraction, set(), set()
        )
        transition_constraints = constraints[1:]

        assert len(transition_constraints) == 1
        depths = self._next_depths(transition_constraints[0])

        assert set(depths["request"]) == {int(dual)}
        assert set(depths["grantA"]) == {int(dual)}
        assert set(depths["roomA"]) == {0}
        assert set(depths["pred_roomA"]) == {1}
        assert set(depths["pred_eff"]) == {0}

        assert set(depths["source_state"]) == {0}
        assert set(depths["target_state"]) == {1}
