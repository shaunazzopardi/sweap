from unittest import TestCase

from programs.program import Program
from programs.transition import Transition
from programs.util import refine_init_values
from prop_lang.biop import BiOp
from prop_lang.types.types import BOOLEAN, INTEGER
from prop_lang.uniop import UniOp
from prop_lang.update import Update
from prop_lang.util import true
from prop_lang.value import Value
from prop_lang.variable import Variable


class TestRefineInitValuesHorizon(TestCase):
    def test_horizon_mode_defaults_vars_even_if_objective_mentions_them(self):
        x = Variable("x")
        y = Variable("y")
        q0 = Variable("q0")
        q1 = Variable("q1")

        transitions = [
            Transition(
                "init_loc",
                BiOp(q0, "&", UniOp("!", q1)),
                [Update(x, Value("0")), Update(y, Value("0"))],
                [],
                "work",
            ),
            Transition(
                "init_loc",
                UniOp("!", BiOp(q0, "&", UniOp("!", q1))),
                [Update(x, x), Update(y, y)],
                [],
                "lose",
            ),
            Transition("work", true(), [Update(x, x), Update(y, y)], [], "work"),
            Transition("lose", true(), [Update(x, x), Update(y, y)], [], "lose"),
        ]

        program = Program(
            name="refine_init_horizon_like_taxi",
            sts=["init_loc", "work", "lose"],
            init_st="init_loc",
            init_values=[("x", INTEGER), ("y", INTEGER)],
            transitions=transitions,
            env_events=[(q0, BOOLEAN), (q1, BOOLEAN)],
            con_events=[],
            preprocess=False,
            emit_state_binary_map=False,
        )

        objective = UniOp(
            "G",
            UniOp(
                "F",
                BiOp(
                    UniOp("X", BiOp(x, "=", Value("0"))),
                    "&",
                    UniOp("X", BiOp(y, "=", Value("0"))),
                ),
            ),
        )

        refine_init_values(
            program,
            objective,
            use_ltl_horizon=True,
            bad_states={"lose"},
        )

        self.assertNotIn("x", program.unset_init_vars)
        self.assertNotIn("y", program.unset_init_vars)
        self.assertEqual(str(program.init_var_values["x"]), "0")
        self.assertEqual(str(program.init_var_values["y"]), "0")
