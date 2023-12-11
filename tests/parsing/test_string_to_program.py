from unittest import TestCase

from parsing.string_to_program import string_to_program


class Test(TestCase):
    def test_string_to_program(self):
        with open('../../examples/parallel/arbiter/program.prog') as file:
            lines = file.readlines()
            program, ltl_spec = string_to_program("\n".join(lines))
            assert ltl_spec is None
            if program == None:
                self.fail()

    def test_string_to_program_with_preds(self):
        with open('../../examples/with_preds/arbiter-paper/program.prog') as file:
            lines = file.readlines()
            program, ltl_spec = string_to_program("\n".join(lines))
            print(ltl_spec)
            if program == None:
                self.fail()
