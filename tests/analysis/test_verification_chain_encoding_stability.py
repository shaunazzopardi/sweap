from contextlib import redirect_stdout
from io import StringIO
from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from config import Config
from analysis.compatibility_checking import strategy_verification as verification
from programs.binary_rep_map import BinaryRepMap
from prop_lang.util import conjunct_formula_set, false, propagate_nexts_and_atomize, true
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.machines.mealy_machine import MealyMachine
from synthesis.machines.moore_machine import MooreMachine


class TestVerificationChainEncodingStability(TestCase):
    def conditions(
        self, regions=6, is_input=False, dual=False,
        machine_type=MealyMachine, owns_bits=False,
    ):
        conf = Config.getConfig()
        self.addCleanup(setattr, conf, "dual", conf.dual)
        conf.dual = dual
        bits, representations = BinaryRepMap.build_binary_rep(
            [Variable(str(i)) for i in range(regions)], "code_"
        )
        chain = SimpleNamespace(bin_vars=bits, bin_rep=representations, is_input=is_input)
        outputs = bits if owns_bits else []
        inputs = [] if owns_bits else bits
        machine = machine_type(
            "strategy", 0,
            inputs if machine_type is MealyMachine else outputs,
            outputs if machine_type is MealyMachine else inputs,
        )
        abstraction = SimpleNamespace(
            get_program=lambda: SimpleNamespace(bin_state_vars=[], out_events=[]),
            get_state_predicates=lambda: set(),
            get_transition_predicates=lambda: set(),
            v_to_chain_pred={"x": chain}, structural_loop_constraints=[],
        )
        with (
            redirect_stdout(StringIO()),
            patch.object(verification, "strategy_to_nuxmv_model"),
            patch.object(verification, "create_nuxmv_model_for_verification_checking", return_value={"main": "model"}),
            patch.object(verification, "there_is_mismatch_between_program_and_controller", return_value=(False, False, "ok")) as check,
        ):
            verification.verify_strategy(
                object(), abstraction, machine,
                true(), SimpleNamespace(init_choice_logic=None),
            )
        return bits, representations, check.call_args.args[2]

    def permits(self, bits, conditions, current, successor):
        condition = propagate_nexts_and_atomize(conjunct_formula_set(conditions))
        values = {}
        for i, bit in enumerate(bits):
            shift = len(bits) - i - 1
            values[bit] = Value("TRUE" if current & (1 << shift) else "FALSE")
            values[Variable(str(bit) + "_next")] = Value(
                "TRUE" if successor & (1 << shift) else "FALSE"
            )
        return condition.replace_formulas(values).to_smt({})[0].simplify().is_true()

    def test_composite_region_cannot_switch_equivalent_codes(self):
        bits, representations, conditions = self.conditions()
        top = representations[Variable("5")]
        self.assertEqual(set(top.variablesin()), set(bits))
        # Six regions use all eight codes; 101, 110 and 111 share the last
        # region. Only its code changes, not the represented predicate values.
        for current in range(8):
            for successor in range(8):
                with self.subTest(current=current, successor=successor):
                    changes_region = min(current, 5) != min(successor, 5)
                    self.assertEqual(
                        changes_region or current == successor,
                        self.permits(bits, conditions, current, successor),
                    )

    def test_exact_codes_are_not_restricted(self):
        bits, _, conditions = self.conditions(regions=4)
        for current in range(4):
            for successor in range(4):
                self.assertTrue(self.permits(bits, conditions, current, successor))

    def test_default_mode_still_skips_input_chains(self):
        _, _, conditions = self.conditions(is_input=True)
        self.assertEqual(conditions, [])

    def test_moore_controller_state_inputs_still_have_stable_codes(self):
        bits, _, conditions = self.conditions(dual=True, machine_type=MooreMachine)
        self.assertFalse(self.permits(bits, conditions, 6, 7))
        self.assertTrue(self.permits(bits, conditions, 6, 6))
        self.assertTrue(self.permits(bits, conditions, 4, 6))

    def test_dual_mode_skips_input_chains(self):
        bits, _, conditions = self.conditions(is_input=True, dual=True)
        self.assertEqual(conditions, [])
        self.assertTrue(self.permits(bits, conditions, 6, 7))
        self.assertTrue(self.permits(bits, conditions, 6, 6))
        self.assertTrue(self.permits(bits, conditions, 4, 6))

    def test_strategy_owned_state_codes_are_not_assumed_stable(self):
        for dual, machine_type in ((False, MooreMachine), (True, MealyMachine)):
            with self.subTest(dual=dual):
                bits, _, conditions = self.conditions(
                    dual=dual, machine_type=machine_type, owns_bits=True,
                )
                self.assertEqual(conditions, [])
                self.assertTrue(self.permits(bits, conditions, 6, 7))

    def test_nonidentity_state_update_does_not_make_false_spec_pass_vacuously(self):
        conf = Config.getConfig()
        self.addCleanup(setattr, conf, "debug", conf.debug)
        conf.debug = False
        model = """MODULE main
            VAR flip : boolean;
                x : integer;
            DEFINE
                code_0 := TRUE;
                code_1 := TRUE;
                code_2 := flip;
            INIT !flip & x = 5
            TRANS next(flip) = !flip & next(x) = x + 1
        """
        for dual, machine_type in ((False, MooreMachine), (True, MealyMachine)):
            with self.subTest(dual=dual), redirect_stdout(StringIO()):
                _, _, conditions = self.conditions(
                    dual=dual, machine_type=machine_type, owns_bits=True,
                )
                contradictory, mismatch, output = (
                    verification.there_is_mismatch_between_program_and_controller(
                        {"main": model}, false(), conditions, 10
                    )
                )
                self.assertFalse(contradictory)
                self.assertTrue(mismatch, output)

    def test_fresh_input_codes_do_not_make_false_spec_pass_vacuously(self):
        conf = Config.getConfig()
        self.addCleanup(setattr, conf, "debug", conf.debug)
        conf.debug = False
        model = """MODULE main
            VAR flip : boolean;
            DEFINE
                code_0 := TRUE;
                code_1 := TRUE;
                code_2 := flip;
                input_value := 5;
            INIT !flip
            TRANS next(flip) = !flip
        """
        for dual in (False, True):
            with self.subTest(dual=dual), redirect_stdout(StringIO()):
                _, _, conditions = self.conditions(is_input=True, dual=dual)
                contradictory, mismatch, output = (
                    verification.there_is_mismatch_between_program_and_controller(
                        {"main": model}, false(), conditions, 10
                    )
                )
                self.assertFalse(contradictory)
                self.assertTrue(mismatch, output)
