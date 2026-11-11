"""Deterministic stress cases for identifier allocation and parser integration."""
from contextlib import redirect_stdout
from io import StringIO
from itertools import product
import random
from unittest import TestCase

import config
from parsing.reserved_names import (
    BOOLEAN_LITERAL_NAMES, is_reserved_name, rename_formula, reserved_name_mapping,
)
from parsing.string_to_issy import string_to_issy
from parsing.string_to_ltl import string_to_ltlmt
from parsing.string_to_ltlmt import ToProgram
from parsing.string_to_program import string_to_program
from parsing.string_to_rpg import rpg_parsec
from prop_lang.variable import Variable


PREFIX = 'res_'
FORMATS = ('sweap', 'issy', 'rpg', 'tsl')
RESERVED = (
    'turn', 'prog', 'process', 'cs', 'pred_x', 'bin_x', 'mismatch',
    'compatible_x', 'guard_x', 'act_x', 'identity_x', 'counterstrategy_guard_x',
    'counterstrategy_act_x', 'floor', 'keep', 'eq_con_x', 'sat_con_x',
    'minigame_event_x', 'env_lose', 'lose', 'curr_i', 'int_x', 'game_x',
    'eval_minigame_x', 'minigame_x', 'con_x', 'c_x', 'q_x', 'eval', 'x_prev',
    'curr_i_prev', 'x_prev_prev', 'init_state', 'second_state', 'compatible',
    'program_state', 'strategy_state', 'prog_m', 'strat_m', 'init_choice_logic',
    '__init', '__trans', '__invar', 'controller_guard_0', 'controller_act_0',
    'program_q_0',
    'comp_pred_x', 'inp_comp_pred_x', 'case', 'esac', 'next', 'self',
    'boolean', 'integer', 'MODULE', 'union', 'xor',
)


class TestReservedNameStress(TestCase):
    def setUp(self):
        conf = config.Config.getConfig()
        old_workers = conf.workers
        conf.workers = 1
        self.addCleanup(setattr, conf, 'workers', old_workers)
        output = redirect_stdout(StringIO())
        output.__enter__()
        self.addCleanup(output.__exit__, None, None, None)

    def test_generated_collision_sets_preserve_names_and_reference_bindings(self):
        rng = random.Random(20261102)
        for batch in range(4):
            prefix = PREFIX
            suffix = '_' + prefix.rstrip('_')
            pool = list(RESERVED) + ['x', 'tRuE', 'fAlSe', 'x_prev_middle', 'true_value']
            pool += [prefix * depth + name for name in RESERVED for depth in (1, 2)]
            pool += [name + suffix * depth for name in RESERVED for depth in (1, 2)]
            for case in range(250):
                declared = set(rng.sample(pool, rng.randint(1, 35)))
                ordered = sorted(declared)
                mapping = reserved_name_mapping(ordered)
                with self.subTest(batch=batch, case=case):
                    rng.shuffle(ordered)
                    self.assertEqual(mapping, reserved_name_mapping(ordered))
                    targets = {mapping.get(n, n) for n in declared}
                    self.assertEqual(len(targets), len(declared))
                    self.assertTrue(all(not is_reserved_name(n) for n in targets))
                    self.assertEqual(reserved_name_mapping(targets), {})
                    for name in declared:
                        for depth, prime in product(range(3), ('', "'")):
                            reference = name + '_prev' * depth
                            # Find the longest explicitly declared root independently
                            # of the mapping's selection of reserved names.
                            roots = [n for n in declared if reference == n or any(
                                reference == n + '_prev' * d for d in (1, 2)
                            )]
                            root = max(roots, key=len)
                            expected = mapping.get(root, root) + reference[len(root):] + prime
                            actual = rename_formula(Variable(reference + prime), mapping)
                            self.assertEqual(str(actual), expected)

    def test_long_prefix_and_suffix_collision_chains(self):
        declarations = {PREFIX * depth + 'curr_i' for depth in range(129)}
        declarations.update('x_prev' + '_res' * depth for depth in range(129))
        mapping = reserved_name_mapping(declarations)
        self.assertEqual(mapping['curr_i'], PREFIX * 129 + 'curr_i')
        self.assertEqual(mapping['x_prev'], 'x_prev' + '_res' * 129)
        self.assertEqual(
            len({mapping.get(name, name) for name in declarations}), len(declarations)
        )

    def test_every_boolean_case_is_either_rejected_or_preserved(self):
        for word in ('true', 'false'):
            for letters in product(*[(c.lower(), c.upper()) for c in word]):
                name = ''.join(letters)
                with self.subTest(name=name):
                    if name in BOOLEAN_LITERAL_NAMES:
                        with self.assertRaises(ValueError):
                            reserved_name_mapping({name})
                    else:
                        self.assertEqual(reserved_name_mapping({name}), {})

    def test_reserved_state_declarations_across_formats(self):
        mixed_case = tuple(
            ''.join(letters) for word in ('true', 'false')
            for letters in product(*[(c.lower(), c.upper()) for c in word])
            if ''.join(letters) not in BOOLEAN_LITERAL_NAMES
        )
        for name in RESERVED + mixed_case + ('true_value', 'false_value', 'truex', 'false1'):
            for kind in FORMATS:
                with self.subTest(name=name, format=kind):
                    target = reserved_name_mapping({name}).get(name, name)
                    if kind == 'sweap':
                        program, objective = string_to_program(f'''
                        program stress {{
                          STATES {{ idle: init }}
                          ENVIRONMENT EVENTS {{ input_value: integer }}
                          CONTROLLER EVENTS {{ }}
                          VALUATION {{ {name}: integer; }}
                          TRANSITIONS {{ idle -> idle [TRUE $ {name} := input_value] }}
                          SPECIFICATION {{ F({name} > 0) }}
                        }}''')
                    elif kind == 'issy':
                        program, objective = string_to_issy(f'''
                        input int input_value
                        state int {name}
                        formula {{ assert F [{name} > 0] }}
                        game Safety from idle {{
                          loc idle 1
                          from idle to idle with [{name}' = input_value]
                        }}''', 'stress')
                    elif kind == 'rpg':
                        program, objective = rpg_parsec(f'''type Safety
input input_value Int
output {name} Int
loc idle 1
init idle
trans idle if (> {name} 0) then sys ((({name} input_value)) idle) else idle
''', 'stress')
                    else:
                        parsed, declarations = string_to_ltlmt(
                            f'guarantee {{ [{name} <- input_value]; G (gt {name} i0()); }}'
                        )
                        program, objective = ToProgram().ltlmt2prog(
                            parsed, var_decs={name: ('var', 'Int'), 'input_value': ('inp', 'Int')}
                        )
                    self.assertIn(Variable(target), program.local_vars)
                    self.assertEqual(program.identifier_renames.get(name, name), target)
                    self.assertTrue(any(
                        Variable(target) in update.variablesin()
                        for transition in program.transitions for update in transition.action
                    ))

    def test_collision_chains_preserve_assignment_sources_across_formats(self):
        for kind in FORMATS:
            with self.subTest(format=kind):
                prefix = PREFIX
                first, second, third = ('curr_i', prefix + 'curr_i', prefix * 2 + 'curr_i')
                declarations = (first, second, third)
                mapping = reserved_name_mapping(declarations)
                if kind == 'sweap':
                    program, _ = string_to_program(f'''
                    program collisions {{
                      STATES {{ idle: init }}
                      ENVIRONMENT EVENTS {{ input_value: integer }}
                      CONTROLLER EVENTS {{ }}
                      VALUATION {{ {' '.join(n + ': integer;' for n in declarations)} }}
                      TRANSITIONS {{ idle -> idle [TRUE $ {first} := {second};
                          {second} := {third}; {third} := input_value] }}
                      SPECIFICATION {{ F({first} > {second}) }}
                    }}''')
                elif kind == 'issy':
                    program, _ = string_to_issy(f'''
                    input int input_value
                    {' '.join('state int ' + n for n in declarations)}
                    formula {{ assert F [{first} > {second}] }}
                    game Safety from idle {{
                      loc idle 1
                      from idle to idle with [{first}' = {second}]
                          && [{second}' = {third}] && [{third}' = input_value]
                    }}''', 'collisions')
                elif kind == 'rpg':
                    program, _ = rpg_parsec(f'''type Safety
input input_value Int
{' '.join('output ' + n + ' Int' for n in declarations)}
loc idle 1
init idle
trans idle sys ((({first} {second}) ({second} {third}) ({third} input_value)) idle)
''', 'collisions')
                else:
                    parsed, _ = string_to_ltlmt(f'''guarantee {{
                        [{first} <- {second}]; [{second} <- {third}];
                        [{third} <- input_value]; G (gt {first} {second});
                    }}''')
                    program, _ = ToProgram().ltlmt2prog(
                        parsed,
                        var_decs={**{n: ('var', 'Int') for n in declarations},
                                  'input_value': ('inp', 'Int')},
                    )
                for left, right in ((first, second), (second, third), (third, 'input_value')):
                    pair = (Variable(mapping.get(left, left)), Variable(mapping.get(right, right)))
                    self.assertTrue(any(
                        (update.left, update.right) == pair
                        for transition in program.transitions for update in transition.action
                    ), pair)

    def test_tsl_comments_do_not_declare_literal_named_outputs(self):
        for comment in ('// [true <- i]\n', '/* [FALSE <- i] */\n'):
            with self.subTest(comment=comment):
                parsed, declarations = string_to_ltlmt(
                    comment + 'guarantee { [x <- i]; G (gt x i0()); }'
                )
                program, _ = ToProgram().ltlmt2prog(
                    parsed, var_decs={'x': ('var', 'Int'), 'i': ('inp', 'Int')}
                )
                self.assertIn(Variable('x'), program.local_vars)
