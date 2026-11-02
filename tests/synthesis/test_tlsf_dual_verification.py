from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import TestCase
from unittest.mock import patch

from pysmt.environment import Environment
from prop_lang.types.types import _typed_var_to_pysmt_type_cached

import config
from parsing.string_to_program import string_to_program
from prop_lang.variable import Variable
from synthesis.synthesis import synthesize


class TestTlsfDualVerification(TestCase):
    def setUp(self):
        # Cached SMT symbols belong to the environment that created them.
        _typed_var_to_pysmt_type_cached.cache_clear()
        self.addCleanup(_typed_var_to_pysmt_type_cached.cache_clear)
        environment = Environment()
        environment.__enter__()
        self.addCleanup(environment.__exit__, None, None, None)
        conf = config.Config.getConfig()
        for attribute, value in (
            ('workers', 1), ('dual', False), ('backend', 'strix'),
            ('verify_controller', False), ('debug', True),
        ):
            old = getattr(conf, attribute)
            setattr(conf, attribute, value)
            self.addCleanup(setattr, conf, attribute, old)
        output = redirect_stdout(StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)

    @staticmethod
    def program(native_true=False):
        source = '''
        program override {
          STATES { a: init, b }
          ENVIRONMENT EVENTS { i: boolean; }
          CONTROLLER EVENTS { o: boolean; }
          VALUATION { }
          TRANSITIONS { a -> b [TRUE], b -> a [TRUE] }
          SPECIFICATION { FALSE }
        }
        '''
        if native_true:
            source = source.replace('SPECIFICATION { FALSE }', 'SPECIFICATION { TRUE }')
        return string_to_program(source)

    def test_dual_loop_receives_the_unshifted_tlsf_objective(self):
        program, native = self.program()
        config.Config.getConfig().dual = True
        with patch('synthesis.synthesis.syfco_ltl', return_value='F(pred_extra)'), patch(
            'synthesis.synthesis.syfco_ltl_in',
            return_value=[Variable('i'), Variable('pred_extra')],
        ), patch('synthesis.synthesis.syfco_ltl_out', return_value=[Variable('o')]), patch(
            'synthesis.synthesis.abstract_synthesis_loop', return_value=object()
        ) as loop:
            synthesize(program, native, 'override.tlsf')
        self.assertEqual(str(loop.call_args.args[3]), 'F(res_pred_extra)')
        self.assertEqual(str(loop.call_args.args[2][0]), 'F(X(res_pred_extra))')
        self.assertNotEqual(loop.call_args.args[3], native)

    def test_dual_without_tlsf_keeps_the_native_objective(self):
        program, native = self.program()
        config.Config.getConfig().dual = True
        with patch('synthesis.synthesis.abstract_synthesis_loop', return_value=object()) as loop:
            synthesize(program, native, None)
        self.assertEqual(loop.call_args.args[3], native)

    def test_real_synthesis_and_verification_use_tlsf_in_both_modes(self):
        for dual in (False, True):
            with self.subTest(dual=dual):
                program, native = self.program()
                state_bit = program.bin_state_vars[0].name
                source = f'''
                INFO {{ TITLE: "independent TLSF events" DESCRIPTION: "regression"
                        SEMANTICS: Mealy TARGET: Mealy }}
                MAIN {{
                  INPUTS {{ i; {state_bit}; pred_extra; x_prev; }}
                  OUTPUTS {{ o; act_extra; }}
                  GUARANTEES {{ G (({state_bit} || pred_extra || x_prev) -> F act_extra); }}
                }}
                '''
                conf = config.Config.getConfig()
                conf.dual = dual
                conf.verify_controller = True
                with TemporaryDirectory(prefix='sweap-tlsf-dual-') as directory:
                    path = Path(directory) / 'override.tlsf'
                    path.write_text(source)
                    wrapped = synthesize(program, native, str(path), bound=3)
                self.assertIsNotNone(wrapped)
                self.assertTrue(wrapped.realisable)
                expected_vars = {
                    Variable('res_' + state_bit), Variable('res_pred_extra'),
                    Variable('x_prev_res'), Variable('res_act_extra'),
                }
                selected = wrapped.verification_context['base_ltl_spec']
                self.assertEqual(set(selected.variablesin()), expected_vars)
                self.assertNotEqual(selected, native)

    def test_real_counterstrategy_verification_uses_tlsf_in_both_modes(self):
        for dual in (False, True):
            with self.subTest(dual=dual):
                program, native = self.program(native_true=True)
                conf = config.Config.getConfig()
                conf.dual = dual
                conf.verify_controller = True
                source = """
                INFO { TITLE: "TLSF counterstrategy" DESCRIPTION: "regression"
                       SEMANTICS: Mealy TARGET: Mealy }
                MAIN {
                  INPUTS { i; pred_extra; }
                  OUTPUTS { o; }
                  GUARANTEES { G pred_extra; }
                }
                """
                with TemporaryDirectory(prefix='sweap-tlsf-counterstrategy-') as directory:
                    path = Path(directory) / 'override.tlsf'
                    path.write_text(source)
                    wrapped = synthesize(program, native, str(path), bound=3)
                self.assertIsNotNone(wrapped)
                self.assertFalse(wrapped.realisable)
                self.assertEqual(
                    str(wrapped.verification_context['base_ltl_spec'].simplify()),
                    'G(res_pred_extra)',
                )
                self.assertNotEqual(wrapped.verification_context['base_ltl_spec'], native)
