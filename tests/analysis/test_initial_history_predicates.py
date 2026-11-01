from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from analysis.compatibility_checking import compatibility_builder as builder
from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl
from analysis.refinement.safety_refinement import interpolation_refinement as refinement
from config import Config
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.types.types import INTEGER
from prop_lang.update import Update
from prop_lang.util import neg, stringify_pred, true
from prop_lang.value import Value
from prop_lang.variable import Variable


def example_program():
    x, y = Variable("x"), Variable("y")
    transition = Transition(
        "run", true(), [Update(x, BiOp(x, "+", Value("1"))), Update(y, Value("0"))],
        [], "run",
    )
    return SimpleNamespace(
        name="history", states={"run"}, initial_state="run", local_vars=[x, y],
        local_vars_str=["x", "y"], symbol_table={"x": INTEGER, "y": INTEGER},
        env_events=[], con_events=[], out_events=[], num_in_out=[], bool_in_out=[],
        init_var_values={}, transitions=[transition], states_binary_map={"run": Variable("run")},
        complete_action_set=lambda actions: actions,
    )


class TestInitialHistoryPredicates(TestCase):
    def test_history_chains_use_the_existing_initial_state_guard(self):
        x, y, previous_y = map(Variable, ("x", "y", "y_prev"))
        predicates = [
            BiOp(x, "<=", Value("0")),
            BiOp(previous_y, "<=", Value("0")),
            BiOp(BiOp(x, "-", previous_y), "<=", Value("0")),
        ]
        chains = [
            SimpleNamespace(term=p.left, bin_rep={p: Variable(f"chain_{i}")})
            for i, p in enumerate(predicates)
        ]
        strategy = StructuredNuXmvModel(
            "strategy", vars=[VarDecl(f"chain_{i}", "boolean") for i in range(3)],
            init=["TRUE"], trans=["TRUE"],
        )
        with patch.object(Config.getConfig(), "dual", False), patch.object(
            builder, "render_structured_model", return_value=""
        ) as render:
            builder.create_nuxmv_model_for_compatibility_checking(
                example_program(), strategy, set(), set(), chains
            )

        definitions = dict(
            entry.split(" := ", 1) for entry in render.call_args.args[0].define
        )
        ordinary = definitions["compatible_state_predicates"]
        guarded = definitions["compatible_tran_predicates"]
        self.assertIn("!init_state", guarded)
        for predicate in predicates:
            flag = stringify_pred(predicate).name
            macro = next(
                name for name, body in definitions.items()
                if name.startswith("comp_") and flag in body
            )
            if predicate.has_prev_vars():
                self.assertIn(macro, guarded)
                self.assertNotIn(macro, ordinary)
            else:
                self.assertIn(macro, ordinary)
                self.assertNotIn(macro, guarded)

    def test_refinement_ignores_initial_history_but_keeps_later_history(self):
        program = example_program()
        predicate = BiOp(Variable("x"), "<=", Variable("y_prev"))
        symbols = {
            name + suffix: INTEGER
            for name in ("x", "y") for suffix in ("", "_prev", "_prev_prev")
        }
        abstraction = SimpleNamespace(get_symbol_table=lambda: symbols)
        states = {stringify_pred(predicate).name: "TRUE"}
        agreed = [
            (program.transitions[0], {"x": "5", "y": "10"}, states),
            (program.transitions[0], {"x": "6", "y": "0"}, states),
        ]

        class EncodingChecked(Exception):
            pass

        def check_encoding(formulas):
            names = [{v.symbol_name() for v in f.get_free_variables()} for f in formulas]
            self.assertFalse(any(name.endswith("_-1") for group in names for name in group))
            # Only the history predicate at step one introduces y_0 here.
            self.assertIn("y_0", names[1])
            raise EncodingChecked

        with patch.object(refinement, "sequence_interpolant", side_effect=check_encoding):
            with self.assertRaises(EncodingChecked):
                refinement.safety_refinement_seq_int(
                    program, abstraction, agreed, ([neg(predicate)], {}), {}, False
                )
