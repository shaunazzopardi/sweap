from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest import TestCase

import config
import parsec
from parsing.string_to_rpg import expr_parser, rpg_parsec


class TestRpgBooleanArity(TestCase):
    def test_singleton_boolean_operators_preserve_their_argument(self):
        parser = expr_parser << parsec.eof()
        expected = parser.parse('(= x 0)')
        for operator in ('and', 'or'):
            with self.subTest(operator=operator):
                self.assertEqual(parser.parse(f'({operator} (= x 0))'), expected)

    def test_singleton_addition_is_still_rejected(self):
        with self.assertRaisesRegex(Exception, 'more than one argument'):
            (expr_parser << parsec.eof()).parse('(+ x)')

    def test_robot_grid_benchmark_parses(self):
        path = Path(__file__).resolve().parents[2] / (
            'benchmarks/rpgsolve/finite/robot-grid-reach-1d-10.rpg'
        )
        conf = config.Config.getConfig()
        old_workers = conf.workers
        conf.workers = 1
        self.addCleanup(setattr, conf, 'workers', old_workers)
        with redirect_stdout(StringIO()):
            program, objective = rpg_parsec(path.read_text(), path.stem)
        self.assertIn('goal', program.states)
        self.assertEqual(str(objective), 'F(goal)')
