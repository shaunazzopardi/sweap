from unittest import TestCase

from parsing.string_to_program import string_to_program


class MyTestCase(TestCase):
    def test_example(self):
        with open('../examples/parallel/arbiter/program.prog') as file:
            lines = file.readlines()
            monitor = string_to_program("\n".join(lines))
            print(monitor)
            if monitor is None:
                self.fail()
        self.assertEqual(True, True)