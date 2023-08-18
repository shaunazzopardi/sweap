from unittest import TestCase

from parsing.string_to_program import string_to_program
from programs.synthesis.synthesis import synthesize


class Test(TestCase):
    def test_synthesize_1(self):
        with open('../examples/parallel/arbiter/program.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_2(self):
        with open('../examples/parallel/arbiter/program2.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_3(self):
        with open('../examples/parallel/arbiter1/program.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter1/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertFalse(real)

    def test_synthesize_4(self):
        with open('../examples/parallel/arbiter2/program.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter2/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_5(self):
        with open('../examples/parallel/arbiter3/program.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_6(self):
        with open('../examples/parallel/arbiter3/program1.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertFalse(real)

    def test_synthesize_7(self):
        with open('../examples/parallel/arbiter3/program2.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_7_5(self):
        with open('../examples/parallel/arbiter3/program3.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertFalse(real)

    def test_synthesize_8(self):
        with open('../examples/parallel/arbiter3/program4.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertFalse(real)

    def test_synthesize_9(self):
        with open('../examples/parallel/arbiter3/program5.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_10(self):
        with open('../examples/parallel/arbiter3/program_no_disj.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertTrue(real)

    def test_synthesize_11(self):
        with open('../examples/parallel/arbiter3/programorig.prog') as program_file:
            program = string_to_program(program_file.read())
            tlsf_file = '../examples/parallel/arbiter3/controller.tlsf'
            (real, mm) = synthesize(program, None, tlsf_file, True, False)
            self.assertFalse(real)

