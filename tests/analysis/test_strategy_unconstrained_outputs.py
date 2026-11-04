from config import Config
from analysis.compatibility_checking.strategy_to_nuxmv import strategy_to_nuxmv_model
from prop_lang.variable import Variable
from synthesis.machines.mealy_machine import MealyMachine


def test_dual_mealy_unmentioned_output_remains_unconstrained(monkeypatch):
    monkeypatch.setattr(Config.getConfig(), "dual", True)
    request, grant, unused = map(Variable, ("request", "grant", "unused"))
    machine = MealyMachine("controller", 0, [request], [grant, unused])
    machine.states = {"st_0", "st_1"}
    machine.transitions = {
        "st_0": {"st_1": {(request, grant)}},
        "st_1": {"st_1": {(request, grant)}},
    }
    model = strategy_to_nuxmv_model(machine, [], [], [], [])
    # It remains an interface variable, but no formula forces either polarity.
    assert any(v.name == "unused" for v in model.vars)
    formulas = "\n".join(model.define + model.init + model.invar + model.trans)
    assert "grant" in formulas
    assert "unused" not in formulas
