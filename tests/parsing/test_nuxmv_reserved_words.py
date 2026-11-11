from contextlib import redirect_stdout
from io import StringIO
from unittest import TestCase
from unittest.mock import patch

from pysmt.environment import Environment

import config
from analysis.compatibility_checking.program_to_nuxmv import (
    create_nuxmv_model, program_to_nuxmv_model,
)
from analysis.model_checker import ModelChecker
from parsing.reserved_names import BOOLEAN_LITERAL_NAMES, NUXMV_RESERVED_WORDS
from parsing.string_to_program import string_to_program
from prop_lang.types.types import _typed_var_to_pysmt_type_cached


class TestNuXmvReservedWords(TestCase):
    def test_keyword_named_declarations_produce_a_valid_nuxmv_model(self):
        # Punctuation and multiword operators cannot be source identifiers.
        words = sorted(name for name in NUXMV_RESERVED_WORDS
                       if name.isidentifier() and name not in BOOLEAN_LITERAL_NAMES)
        declarations = ' '.join(name + ': integer;' for name in words)
        assignments = '; '.join(name + ' := input_value' for name in words)
        source = f'''
        program keywords {{
          STATES {{ idle: init }}
          ENVIRONMENT EVENTS {{ input_value: integer }}
          CONTROLLER EVENTS {{ }}
          VALUATION {{ {declarations} }}
          TRANSITIONS {{ idle -> idle [TRUE $ {assignments}] }}
          SPECIFICATION {{ G(idle) }}
        }}
        '''
        _typed_var_to_pysmt_type_cached.cache_clear()
        self.addCleanup(_typed_var_to_pysmt_type_cached.cache_clear)
        with Environment(), patch.object(config.Config.getConfig(), 'workers', 1), redirect_stdout(StringIO()):
            program, _ = string_to_program(source)
            for name in words:
                self.assertIn('res_' + name, program.symbol_table)
                self.assertNotIn(name, program.local_vars_str)
            model = create_nuxmv_model(program_to_nuxmv_model(program))
            result, _ = ModelChecker().invar_check(model, 'TRUE', None, False)
            self.assertTrue(result)
