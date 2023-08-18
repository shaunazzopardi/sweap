from unittest import TestCase

from parsing.string_to_program import string_to_program


class Test(TestCase):
    def test_string_to_program(self):
        with open('../examples/parallel/arbiter/program.prog') as file:
            lines = file.readlines()
            program = string_to_program("\n".join(lines))
            if program == None:
                self.fail()
