"""Both synthesis modes use the unified compatibility checker."""

from unittest.mock import patch
import pytest
from config import Config
from analysis.refinement.refinement import refinement_standard


@pytest.mark.parametrize("dual", [False, True])
@pytest.mark.parametrize("controller", [False, True])
def test_refinement_uses_unified_compatibility_checker(dual, controller, monkeypatch):
    monkeypatch.setattr(Config.getConfig(), "dual", dual)
    program, abstraction, machine, problem = [object() for _ in range(4)]
    with patch(
        "analysis.refinement.refinement.compatibility_checking",
        return_value=(True, "ok"),
    ) as checker:
        compatible, result = refinement_standard(
            program, abstraction, machine, controller, {}, 0, problem, False
        )
    checker.assert_called_once_with(program, abstraction, machine, problem, controller)
    assert compatible
    assert result is machine
