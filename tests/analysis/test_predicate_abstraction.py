from unittest import TestCase

from programs.analysis.model_checker import ModelChecker
from programs.abstraction.predicate_abstraction import abstraction_to_ltl_with_turns, predicate_abstraction_init
from parsing.string_to_program import string_to_program
from programs.util import create_nuxmv_model, symbol_table_from_program


class Test(TestCase):
    def test_abstraction_to_ltl_with_turns(self):
        with open('../../examples/parallel/arbiter/program.prog') as file:
            data = file.read()
            program = string_to_program(data)
            model_checker = ModelChecker()
            nuxmv_model = create_nuxmv_model(program.to_nuXmv_with_turns())
            abstraction, _, _ = predicate_abstraction_init(program, [], [], program.symbol_table, False)
            ltl_abstraction = abstraction_to_ltl_with_turns(abstraction)
            print(ltl_abstraction)
            out = model_checker.check(nuxmv_model, str(ltl_abstraction), None, False)
            if not out[0]:
                print(out[1])
            assert (out[0] is True)
