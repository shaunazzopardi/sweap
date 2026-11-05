"""Exercise nuXmv's model/property boundary and error propagation."""

import os

import pytest

from analysis.model_checker import ModelChecker, nuxmv_path


pytestmark = pytest.mark.skipif(
    not os.access(nuxmv_path, os.X_OK), reason="nuXmv binary is required"
)


@pytest.mark.parametrize("mc", [False, True], ids=["invariant", "ltl"])
@pytest.mark.parametrize("expected", [False, True])
def test_large_property_is_checked_in_main_by_name(mc, expected):
    # Both existing properties have the opposite verdict. The requested
    # property must be selected by name, independently of property ordering.
    opposite = "FALSE" if expected else "TRUE"
    model = {"main": f"""MODULE main
VAR x : boolean;
ASSIGN init(x) := TRUE; next(x) := x;
LTLSPEC NAME __sweap_check := {opposite};
INVARSPEC {opposite};
""", "helper": """MODULE helper
VAR x : boolean;
ASSIGN init(x) := FALSE; next(x) := x;
"""}
    original = dict(model)
    formula = "x" if expected else "!x"
    # Balanced conjunctions exceed the command interpreter's input limit
    # without creating a deep syntax tree. These depend on the model's x.
    for _ in range(14):
        formula = f"({formula} & {formula})"
    if mc:
        formula = "G (" + formula + ")"
    assert len(formula) > 65536
    verdict, _ = ModelChecker().invar_check(model, formula, 5, mc)
    assert verdict is expected
    assert model == original


@pytest.mark.parametrize("mc", [False, True])
def test_invalid_property_reports_parser_error(mc):
    with pytest.raises(RuntimeError, match=r"(?s)nuXmv failed.*syntax error"):
        ModelChecker().invar_check({"main": "MODULE main\n"}, "TRUE & )", 5, mc)


def test_invalid_model_reports_parser_error():
    with pytest.raises(RuntimeError, match=r"(?s)nuXmv failed.*syntax error"):
        ModelChecker().invar_check({"main": "MODULE main\nVAR x : ;\n"}, "TRUE", 5, True)


def test_checks_reuse_modules_without_accumulating_properties():
    modules = {
        "helper": "MODULE helper\nVAR x : boolean;\nINVAR !x\n",
        "main": "MODULE main\nVAR x : boolean;\nINVAR x\n",
    }
    original = dict(modules)
    checker = ModelChecker()
    assert checker.invar_check(modules, "x", None, False)[0] is True
    assert checker.invar_check(modules, "!x", None, False)[0] is False
    assert modules == original


def test_missing_main_is_rejected():
    with pytest.raises(ValueError, match="no main module"):
        ModelChecker().invar_check({"helper": "MODULE helper\n"}, "TRUE", None, False)


def test_vmt_property_stays_in_main_without_mutating_modules(monkeypatch, tmp_path):
    from pathlib import Path
    from analysis import model_checker

    modules = {
        "main": "MODULE main\nVAR x : boolean;\nINVAR x\n",
        "helper": "MODULE helper\nVAR x : boolean;\nINVAR !x\n",
    }
    original = dict(modules)
    captured = []

    def run(command, **kwargs):
        captured.append(Path(command[-1]).read_text())
        return "exported"

    monkeypatch.setattr(model_checker.subprocess, "check_output", run)
    ModelChecker().to_vmt(modules, "G x", str(tmp_path / "model"))
    assert captured == [modules["main"] + "\nLTLSPEC G x;\n\n" + modules["helper"]]
    assert modules == original
