from unittest import TestCase

from analysis.compatibility_checking.compatibility_checking import create_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.string_to_program import string_to_program


class TestModelChecker(TestCase):
    def test_check(self):
        with open('../../examples/parallel/arbiter/program.prog') as file:
            data = file.read()
            program = string_to_program(data)
            model_checker = ModelChecker()
            nuxmv_model = create_nuxmv_model(program.to_nuXmv_with_turns())
            out = model_checker.invar_check(nuxmv_model, "F FALSE", None)
            print(out[1])
            assert (out[0] is False)
