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
from parsing.string_to_rpg import rpg_parsec
from parsing.string_to_issy import string_to_issy
from parsing.string_to_ltl import string_to_ltlmt
from parsing.string_to_ltlmt import ToProgram
from prop_lang.variable import Variable
from prop_lang.types.types import BOOLEAN
from synthesis.synthesis import extract_init_preds, process_specifications, synthesize


class TestTlsfReservedNames(TestCase):
    def setUp(self):
        # Cached SMT symbols belong to the environment that created them.
        _typed_var_to_pysmt_type_cached.cache_clear()
        self.addCleanup(_typed_var_to_pysmt_type_cached.cache_clear)
        environment = Environment()
        environment.__enter__()
        self.addCleanup(environment.__exit__, None, None, None)
        conf = config.Config.getConfig()
        for attribute, value in (('workers', 1), ('dual', False)):
            old = getattr(conf, attribute)
            setattr(conf, attribute, value)
            self.addCleanup(setattr, conf, attribute, old)
        output = redirect_stdout(StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)

    @staticmethod
    def program(native_spec=True):
        return string_to_program('''
        program external_spec {
          STATES { q: init }
          ENVIRONMENT EVENTS {
            curr_i: boolean; res_curr_i: boolean; pred_request: boolean;
          }
          CONTROLLER EVENTS { act_grant: boolean; }
          VALUATION { curr_count: integer := 0; }
          TRANSITIONS { q -> q [TRUE $ curr_count := curr_count + 1] }
        ''' + ('SPECIFICATION { G(q) }' if native_spec else '') + '}')

    def process(self, program, native, formula, inputs=None, outputs=None):
        if inputs is None:
            inputs = ['curr_i', 'res_curr_i', 'pred_request']
        if outputs is None:
            outputs = ['act_grant']
        with patch('synthesis.synthesis.syfco_ltl', return_value=formula), patch(
            'synthesis.synthesis.syfco_ltl_in', return_value=list(map(Variable, inputs))
        ), patch(
            'synthesis.synthesis.syfco_ltl_out', return_value=list(map(Variable, outputs))
        ):
            return process_specifications(program, native, 'external.tlsf')

    def test_reserved_signals_and_prefix_collisions_use_program_mapping(self):
        program, native = self.program()
        assumptions, guarantees, inputs, outputs = self.process(
            program, native, 'G((curr_i & res_curr_i & pred_request) -> F(act_grant))'
        )
        self.assertEqual(set(inputs), {
            Variable('res_res_curr_i'), Variable('res_curr_i'),
            Variable('res_pred_request'),
        })
        self.assertEqual(outputs, [Variable('res_act_grant')])
        self.assertEqual(set(guarantees[0].variablesin()), set(inputs + outputs))
        self.assertTrue(assumptions[0].is_true())

    def test_implicit_lookbacks_follow_renamed_state(self):
        program, native = self.program()
        _, guarantees, _, _ = self.process(
            program, native, 'X(curr_count_prev >= 0)'
        )
        self.assertEqual(
            set(guarantees[0].variablesin()), {Variable('res_curr_count_prev')}
        )

    def test_tlsf_only_signal_cannot_alias_a_generated_program_name(self):
        program, native = string_to_program('''
        program signal_collision {
          STATES { q: init }
          ENVIRONMENT EVENTS { curr_i: boolean; }
          CONTROLLER EVENTS { }
          VALUATION { }
          TRANSITIONS { q -> q [TRUE] }
          SPECIFICATION { G(q) }
        }
        ''')
        _, guarantees, inputs, _ = self.process(
            program, native, 'G(curr_i & res_curr_i)',
            inputs=['curr_i', 'res_curr_i'], outputs=[],
        )
        self.assertEqual(set(inputs), {
            Variable('res_curr_i'), Variable('res_res_curr_i'),
        })
        self.assertEqual(set(guarantees[0].variablesin()), set(inputs))

    def test_missing_program_signals_are_still_rejected(self):
        program, native = self.program()
        for overrides, message in (
            ({'inputs': ['curr_i', 'res_curr_i']}, 'different input variables'),
            ({'outputs': ['wrong_output']}, 'different output variables'),
        ):
            with self.subTest(overrides=overrides):
                with self.assertRaisesRegex(Exception, message):
                    self.process(program, native, 'TRUE', **overrides)

    def test_tlsf_signals_cannot_use_boolean_literal_names(self):
        program, native = self.program()
        for name in ('true', 'false', 'TRUE', 'FALSE', 'True', 'False'):
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, 'Boolean literal'):
                    self.process(program, native, 'TRUE', outputs=[name])

    def test_tlsf_can_supply_the_only_objective(self):
        program, native = self.program(native_spec=False)
        self.assertIsNone(native)
        _, guarantees, _, _ = self.process(program, native, 'F(curr_i)')
        self.assertEqual(
            set(guarantees[0].variablesin()), {Variable('res_res_curr_i')}
        )

    def test_real_syfco_expands_reserved_tlsf_definitions_before_renaming(self):
        program, native = self.program(native_spec=False)
        source = '''
        INFO { TITLE: "reserved identifiers" DESCRIPTION: "regression"
               SEMANTICS: Mealy TARGET: Mealy }
        GLOBAL { DEFINITIONS { pred_alias = curr_i && pred_request; } }
        MAIN {
          INPUTS { curr_i; res_curr_i; pred_request; }
          OUTPUTS { act_grant; }
          GUARANTEES { G (pred_alias -> F act_grant); }
        }
        '''
        with TemporaryDirectory(prefix='sweap-tlsf-names-') as directory:
            path = Path(directory) / 'external.tlsf'
            path.write_text(source)
            _, guarantees, _, outputs = process_specifications(program, native, str(path))
        self.assertEqual(outputs, [Variable('res_act_grant')])
        self.assertEqual(set(guarantees[0].variablesin()), {
            Variable('res_res_curr_i'), Variable('res_pred_request'),
            Variable('res_act_grant'),
        })

    @staticmethod
    def two_state_program():
        return string_to_program("""
        program independent {
          STATES { a: init, b }
          ENVIRONMENT EVENTS { i: boolean; }
          CONTROLLER EVENTS { o: boolean; }
          VALUATION { }
          TRANSITIONS { a -> b [TRUE], b -> a [TRUE] }
          SPECIFICATION { G(a | b) }
        }
        """)

    def test_tlsf_only_signals_remain_independent_through_abstraction(self):
        program, native = self.two_state_program()
        state_bit = program.bin_state_vars[0]
        assumptions, guarantees, inputs, outputs = self.process(
            program, native, f'G(({state_bit} | pred_extra | x_prev) -> F(act_extra))',
            inputs=['i', str(state_bit), 'pred_extra', 'x_prev', 'res_pred_extra'],
            outputs=['o', 'act_extra'],
        )
        self.assertIn(Variable('res_' + str(state_bit)), inputs)
        self.assertNotIn(state_bit, inputs)
        self.assertIn(Variable('res_res_pred_extra'), inputs)
        self.assertIn(Variable('res_pred_extra'), inputs)
        self.assertIn(Variable('x_prev_res'), inputs)
        self.assertIn(Variable('res_act_extra'), outputs)
        for signal in inputs + outputs:
            self.assertEqual(program.symbol_table[str(signal)], BOOLEAN)
            self.assertIn(signal, program.bool_in_out)
            self.assertNotIn(signal, program.local_vars)
        self.assertIn(state_bit.name, program.symbol_table)
        predicates, *_ = extract_init_preds(program, assumptions, guarantees)
        self.assertTrue(set(inputs + outputs).isdisjoint(predicates))

    def test_tlsf_registration_is_idempotent_and_does_not_require_old_extras(self):
        program, native = self.two_state_program()
        for _ in range(2):
            self.process(program, native, 'G(pred_extra -> F(o))',
                         inputs=['i', 'pred_extra'], outputs=['o'])
        self.assertEqual(program.inputs.count(Variable('res_pred_extra')), 1)
        self.assertEqual(program.bool_in_out.count(Variable('res_pred_extra')), 1)
        _, _, inputs, outputs = self.process(
            program, native, 'G(i -> F(o))', inputs=['i'], outputs=['o']
        )
        self.assertEqual(inputs, [Variable('i')])
        self.assertEqual(outputs, [Variable('o')])

    def test_redeclared_program_input_as_tlsf_output_is_rejected(self):
        program, native = self.two_state_program()
        with self.assertRaisesRegex(ValueError, 'different input variables'):
            self.process(program, native, 'G(i)', inputs=[], outputs=['i', 'o'])

    def test_external_tlsf_is_rejected_for_other_input_formats(self):
        rpg, rpg_spec = rpg_parsec("""type Safety
output x Int
loc q 1
init q
trans q sys (((x 0)) q ((x 1)) q)
""", 'generated_actions')
        issy, issy_spec = string_to_issy("""
        input bool i_issy
        state bool x_issy
        def pred_alias = x_issy
        formula { assert G pred_alias }
        game Safety from a {
          loc a 1
          from a to a with [x_issy' = i_issy]
        }
        """, 'macro_alias')
        parsed, _ = string_to_ltlmt('guarantee { [x_tsl <- i_tsl]; G (gt x_tsl i0()); }')
        tsl, tsl_spec = ToProgram().ltlmt2prog(
            parsed, var_decs={'x_tsl': ('var', 'Int'), 'i_tsl': ('inp', 'Int')}
        )
        for program, native in ((rpg, rpg_spec), (issy, issy_spec), (tsl, tsl_spec)):
            with self.subTest(format=program.input_format):
                with patch('synthesis.synthesis.syfco_ltl') as syfco:
                    with self.assertRaisesRegex(ValueError, r'only supported with \.prog'):
                        process_specifications(program, native, 'external.tlsf')
                    syfco.assert_not_called()
                # Their own embedded objectives remain usable.
                process_specifications(program, native, None)

    def test_framework_marker_names_are_independent_in_real_verification(self):
        conf = config.Config.getConfig()
        for marker in (
            'init_state', 'second_state', 'compatible', 'program_state',
            'strategy_state', 'prog_m', 'strat_m', 'init_choice_logic',
            '__init', '__trans', '__invar', 'controller_guard_0',
            'controller_act_0', 'program_q_0',
            'comp_pred__cnt_LTEQ_0_', 'inp_comp_pred__cnt_LTEQ_0_',
            'case', 'esac', 'next', 'self',
        ):
            for dual in (False, True):
                for role in ('input', 'output'):
                    with self.subTest(marker=marker, dual=dual, role=role):
                        program, _ = self.two_state_program()
                        inputs = 'i; ' + (marker + ';' if role == 'input' else '')
                        outputs = 'o; ' + (marker + ';' if role == 'output' else '')
                        goal = f'F !{marker}' if role == 'input' else f'G {marker}'
                        source = f"""
                        INFO {{ TITLE: "framework names" DESCRIPTION: "regression"
                                SEMANTICS: Mealy TARGET: Mealy }}
                        MAIN {{
                          INPUTS {{ {inputs} }}
                          OUTPUTS {{ {outputs} }}
                          GUARANTEES {{ {goal}; }}
                        }}
                        """
                        with TemporaryDirectory(prefix='sweap-marker-names-') as directory:
                            path = Path(directory) / 'markers.tlsf'
                            path.write_text(source)
                            with patch.object(conf, 'dual', dual), patch.object(
                                conf, 'backend', 'strix'
                            ), patch.object(conf, 'verify_controller', True):
                                wrapped = synthesize(program, None, str(path), bound=3)
                        self.assertIsNotNone(wrapped)
                        self.assertEqual(wrapped.realisable, role == 'output')
                        selected = wrapped.verification_context['base_ltl_spec']
                        self.assertEqual(set(selected.variablesin()), {Variable('res_' + marker)})

    def test_unused_reserved_tlsf_inputs_do_not_conflict_with_model_definitions(self):
        conf = config.Config.getConfig()
        for marker in ('__init', '__trans', '__invar', 'controller_guard_0',
                       'controller_act_0', 'program_q_0'):
            for dual in (False, True):
                with self.subTest(marker=marker, dual=dual):
                    program, _ = self.two_state_program()
                    source = f"""
                    INFO {{ TITLE: "unused reserved signal" DESCRIPTION: "regression"
                            SEMANTICS: Mealy TARGET: Mealy }}
                    MAIN {{
                      INPUTS {{ i; {marker}; }}
                      OUTPUTS {{ o; }}
                      GUARANTEES {{ G o; }}
                    }}
                    """
                    with TemporaryDirectory(prefix='sweap-unused-names-') as directory:
                        path = Path(directory) / 'unused.tlsf'
                        path.write_text(source)
                        with patch.object(conf, 'dual', dual), patch.object(
                            conf, 'backend', 'strix'
                        ), patch.object(conf, 'verify_controller', True):
                            wrapped = synthesize(program, None, str(path), bound=3)
                    self.assertIsNotNone(wrapped)
                    self.assertTrue(wrapped.realisable)
                    self.assertIn(Variable('res_' + marker), program.inputs)
                    self.assertNotIn(Variable(marker), program.inputs)

    def test_unused_compatibility_macro_names_are_safe_with_arithmetic_predicates(self):
        conf = config.Config.getConfig()
        markers = (
            'comp_pred__cnt_LTEQ_0_', 'comp_pred__NEG__cnt_LTEQ_0_',
            'inp_comp_pred__cnt_LTEQ_0_',
        )
        path = Path(__file__).resolve().parents[1] / 'test-problems' / 'program2.prog'
        program, _ = string_to_program(path.read_text())
        source = f"""
        INFO {{ TITLE: "compatibility names" DESCRIPTION: "regression"
                SEMANTICS: Mealy TARGET: Mealy }}
        MAIN {{
          INPUTS {{ request; {' '.join(name + ';' for name in markers)} }}
          OUTPUTS {{ grant; }}
          GUARANTEES {{ G grant; }}
        }}
        """
        with TemporaryDirectory(prefix='sweap-compatibility-names-') as directory:
            tlsf = Path(directory) / 'compatibility.tlsf'
            tlsf.write_text(source)
            with patch.object(conf, 'dual', False), patch.object(
                conf, 'backend', 'strix'
            ), patch.object(conf, 'verify_controller', True):
                wrapped = synthesize(program, None, str(tlsf), bound=3)
        self.assertIsNotNone(wrapped)
        self.assertTrue(wrapped.realisable)
        for name in markers:
            self.assertIn(Variable('res_' + name), program.inputs)
            self.assertNotIn(Variable(name), program.inputs)

    @staticmethod
    def state_output_program():
        return string_to_program('''
        program output_roles {
          STATES { q: init }
          ENVIRONMENT EVENTS { i: boolean; }
          CONTROLLER EVENTS { o: boolean; }
          VALUATION {
            flag: boolean := FALSE;
            next: boolean := FALSE;
            fixed_flag: boolean := TRUE;
            count_value: integer := 0;
          }
          TRANSITIONS { q -> q [TRUE $ flag := !flag; next := !next;
                                      count_value := count_value + 1] }
          SPECIFICATION { G(q) }
        }
        ''')

    def test_program_state_identifiers_cannot_be_tlsf_outputs(self):
        program, native = self.state_output_program()
        original_inputs = list(program.inputs)
        original_outputs = list(program.outputs)
        original_symbols = dict(program.symbol_table)
        for dual in (False, True):
            for name in ('flag', 'next', 'fixed_flag', 'count_value', 'q'):
                with self.subTest(name=name, dual=dual), patch.object(
                    config.Config.getConfig(), 'dual', dual
                ):
                    with self.assertRaisesRegex(
                        ValueError, f"TLSF output {name!r}.*not a controller output"
                    ):
                        self.process(
                            program, native, 'TRUE', inputs=['i', 'free_input'],
                            outputs=['o', name, 'free_output'],
                        )
                    # Reject the interface before registering any extra signals.
                    self.assertEqual(program.inputs, original_inputs)
                    self.assertEqual(program.outputs, original_outputs)
                    self.assertEqual(program.symbol_table, original_symbols)
                    self.assertEqual(program.tlsf_inputs, {})
                    self.assertEqual(program.tlsf_outputs, {})

    def test_real_tlsf_state_outputs_are_rejected_even_if_objective_is_tautological(self):
        for name in ('flag', 'q'):
            with self.subTest(name=name):
                program, native = self.state_output_program()
                source = f'''
                INFO {{ TITLE: "invalid output role" DESCRIPTION: "regression"
                        SEMANTICS: Mealy TARGET: Mealy }}
                MAIN {{
                  INPUTS {{ i; }}
                  OUTPUTS {{ o; {name}; }}
                  GUARANTEES {{ G ({name} || !{name}); }}
                }}
                '''
                with TemporaryDirectory(prefix='sweap-output-roles-') as directory:
                    path = Path(directory) / 'roles.tlsf'
                    path.write_text(source)
                    with self.assertRaisesRegex(ValueError, 'not a controller output'):
                        process_specifications(program, native, str(path))

    def test_controller_and_independent_tlsf_outputs_are_preserved(self):
        program, native = self.state_output_program()
        _, guarantees, inputs, outputs = self.process(
            program, native, 'G(o | act_extra)',
            inputs=['i'], outputs=['o', 'act_extra'],
        )
        self.assertEqual(inputs, [Variable('i')])
        self.assertEqual(outputs, [Variable('o'), Variable('res_act_extra')])
        self.assertEqual(set(guarantees[0].variablesin()), set(outputs))
        self.assertIn(Variable('res_act_extra'), program.outputs)

    def test_numeric_tlsf_inputs_are_rejected_before_registering_signals(self):
        program, native = string_to_program('''
        program typed_inputs {
          STATES { q: init }
          ENVIRONMENT EVENTS { i: boolean; u: integer; }
          CONTROLLER EVENTS { o: boolean; }
          VALUATION { counter: integer := 0; fixed_number: integer := 0; }
          TRANSITIONS { q -> q [TRUE $ counter := counter + 1] }
          SPECIFICATION { G(q) }
        }
        ''')
        for dual in (False, True):
            for name in ('u', 'counter', 'fixed_number'):
                for formula in ('TRUE', f'G({name})'):
                    with self.subTest(dual=dual, name=name, formula=formula), patch.object(
                        config.Config.getConfig(), 'dual', dual
                    ):
                        with self.assertRaisesRegex(ValueError, 'requires a Boolean'):
                            self.process(program, native, formula,
                                         inputs=['i', name, 'extra'], outputs=['o'])
                        self.assertEqual(program.tlsf_inputs, {})
                        self.assertNotIn(Variable('extra'), program.inputs)

    def test_boolean_observers_and_projected_constants_are_valid_inputs(self):
        program, native = self.state_output_program()
        _, guarantees, _, _ = self.process(
            program, native, 'G(flag & fixed_flag)',
            inputs=['i', 'flag', 'fixed_flag'], outputs=['o'],
        )
        self.assertEqual(set(guarantees[0].variablesin()), {Variable('flag')})

    def test_native_and_tlsf_share_removed_states_and_valuation_constants(self):
        program, native = string_to_program('''
        program constants {
          STATES { q: init, unreachable }
          ENVIRONMENT EVENTS { i: boolean; }
          CONTROLLER EVENTS { o: boolean; }
          VALUATION { fixed_flag: boolean := TRUE; fixed_number: integer := 0; }
          TRANSITIONS { q -> q [TRUE], unreachable -> unreachable [TRUE] }
          SPECIFICATION { G(!unreachable & fixed_flag & (fixed_number = 0)) }
        }
        ''')
        self.assertTrue(program.specification_constants[Variable('unreachable')].is_false())
        self.assertNotIn(Variable('unreachable'), program.constants)
        self.assertFalse(native.variablesin())
        for dual in (False, True):
            with self.subTest(dual=dual), patch.object(config.Config.getConfig(), 'dual', dual):
                _, guarantees, _, _ = self.process(
                    program, native, 'G(!unreachable & fixed_flag & (fixed_number = 0))',
                    inputs=['i', 'unreachable', 'fixed_flag'], outputs=['o'],
                )
                self.assertFalse(guarantees[0].variablesin())
        with self.assertRaisesRegex(ValueError, 'Invalid history reference'):
            self.process(program, native, 'X(unreachable_prev)', inputs=['i'], outputs=['o'])

    def test_removed_state_tlsf_objectives_synthesise_and_verify(self):
        conf = config.Config.getConfig()
        for dual in (False, True):
            for goal, expected in (('F unreachable', False), ('G !unreachable', True)):
                with self.subTest(dual=dual, goal=goal):
                    program, native = string_to_program('''
                    program pruned {
                      STATES { q: init, unreachable }
                      ENVIRONMENT EVENTS { i: boolean; }
                      CONTROLLER EVENTS { o: boolean; }
                      VALUATION { }
                      TRANSITIONS { q -> q [TRUE], unreachable -> unreachable [TRUE] }
                      SPECIFICATION { G(q) }
                    }
                    ''')
                    source = f'''
                    INFO {{ TITLE: "removed state" DESCRIPTION: "regression"
                            SEMANTICS: Mealy TARGET: Mealy }}
                    MAIN {{ INPUTS {{ i; unreachable; }} OUTPUTS {{ o; }}
                            GUARANTEES {{ {goal}; }} }}
                    '''
                    with TemporaryDirectory(prefix='sweap-constants-') as directory:
                        path = Path(directory) / 'constants.tlsf'
                        path.write_text(source)
                        with patch.object(conf, 'dual', dual), patch.object(
                            conf, 'backend', 'strix'
                        ), patch.object(conf, 'verify_controller', True):
                            wrapped = synthesize(program, native, str(path), bound=3)
                    self.assertEqual(wrapped.realisable, expected)
                    self.assertFalse(wrapped.verification_context['base_ltl_spec'].variablesin())
