import pytest
from types import SimpleNamespace
from unittest.mock import patch
from analysis.compatibility_checking.compatibility_builder import (
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.compatibility_checking.compatibility_checking import (
    there_is_mismatch_between_program_and_strategy,
)
from analysis.compatibility_checking.types import StructuredNuXmvModel
from config import Config
from prop_lang.variable import Variable


def test_dual_second_state_tracks_first_program_step(monkeypatch):
    monkeypatch.setattr(Config.getConfig(), "dual", True)
    program = SimpleNamespace(
        states={"q0"},
        states_binary_map={"q0": Variable("q0")},
        num_in_out=[],
        deterministic=True,
    )
    model = StructuredNuXmvModel(
        name="prog", vars=[], define=[], init=["TRUE"], invar=["TRUE"], trans=["TRUE"]
    )
    strategy = StructuredNuXmvModel(
        name="controller",
        vars=[],
        define=[],
        init=["TRUE"],
        invar=["TRUE"],
        trans=["TRUE"],
    )
    with patch(
        "analysis.compatibility_checking.compatibility_builder.program_to_nuxmv_model",
        return_value=model,
    ):
        text = create_nuxmv_model_for_compatibility_checking(
            program, strategy, set(), set(), []
        )
    text = "\n".join(text.values())
    assert "init_state <-> next(second_state)" in text
    assert "!next(init_state)" in text
    assert "!second_state" in text
    assert "turn =" not in text


@pytest.mark.parametrize("debug", [False, True])
def test_dual_controller_checks_compatibility_and_debug_deadlocks(monkeypatch, debug):
    conf = Config.getConfig()
    for key in ("dual", "mc"):
        monkeypatch.setattr(conf, key, True)
    monkeypatch.setattr(conf, "debug", debug)
    with patch(
        "analysis.compatibility_checking.compatibility_checking.ModelChecker.invar_check",
        side_effect=[(True, "compatible"), (True, "deadlock")],
    ) as check:
        result = there_is_mismatch_between_program_and_strategy(
            {"main": "MODULE main"}, controller=True
        )
    assert result == (
        (True, None, "deadlock") if debug else (False, False, "compatible")
    )
    assert check.call_count == (2 if debug else 1)
    assert check.call_args_list[0].args[1] == "compatible"
    if debug:
        assert check.call_args_list[1].args[1] == "(G compatible) -> F FALSE"
