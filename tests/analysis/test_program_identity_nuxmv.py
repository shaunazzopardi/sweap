from types import SimpleNamespace
from unittest import TestCase

from analysis.compatibility_checking.program_to_nuxmv import (
    create_nuxmv_model,
    program_to_nuxmv_model,
)
from analysis.model_checker import ModelChecker
from config import Config
from programs.transition import Transition
from prop_lang.types.types import INTEGER
from prop_lang.util import true
from prop_lang.variable import Variable


def program(states=("q",), local=False, output=False):
    x = Variable("x")
    return SimpleNamespace(
        name="smoke", states=set(states), initial_state=states[0],
        transitions=[Transition(states[0], true(), [], [], states[0])],
        local_vars_str=["x"] if local else [], local_vars=[x] if local else [],
        out_events=[Variable("event")] if output else [],
        num_in_out=[], bool_in_out=[Variable("b")],
        symbol_table={"x": INTEGER} if local else {}, init_var_values={},
        complete_action_set=lambda action: action,
    )


class TestProgramIdentityNuXmv(TestCase):
    def test_empty_identity_is_true_in_both_modes(self):
        conf = Config.getConfig()
        self.addCleanup(setattr, conf, "dual", conf.dual)
        for dual in (False, True):
            conf.dual = dual
            with self.subTest(dual=dual):
                model = program_to_nuxmv_model(program())
                self.assertIn("identity_smoke := TRUE", model.define)
                text = create_nuxmv_model(model)
                self.assertIn("identity_smoke := TRUE;", text["main"])
                valid, _ = ModelChecker().invar_check(text, "identity_smoke", None, False)
                self.assertTrue(valid)

    def test_nonempty_identity_keeps_variable_and_output_constraints(self):
        model = program_to_nuxmv_model(program(local=True, output=True))
        self.assertIn("identity_smoke := next(x) = x & !next(event)", model.define)

    def test_multiple_locations_still_keep_the_program_state(self):
        model = program_to_nuxmv_model(program(states=("q", "r")))
        self.assertIn("identity_smoke := next(program_state) = program_state", model.define)
