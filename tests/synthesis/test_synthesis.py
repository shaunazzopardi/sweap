import time
from unittest import TestCase

from parsing.string_to_program import string_to_program
from synthesis.synthesis import synthesize
import logging

logging.basicConfig(filename="tests" + str(time.time()) + ".log",
                    encoding='utf-8',
                    level=logging.INFO,
                    format='%(asctime)s %(levelname)-8s %(message)s',
                    datefmt='%Y-%m-%d %H:%M:%S')


class Test(TestCase):
    def test_synthesize_1(self):
        logging.info("Starting test_synthesize_1")
        with open('./examples/with_preds/arbiter/program.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_2(self):
        logging.info("Starting test_synthesize_2")
        with open('./examples/with_preds/arbiter/program2.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_3(self):
        logging.info("Starting test_synthesize_3")
        with open('./examples/with_preds/arbiter/program3.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertFalse(real)

    def test_synthesize_4(self):
        logging.info("Starting test_synthesize_4")
        with open('./examples/with_preds/arbiter/program4.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_5(self):
        logging.info("Starting test_synthesize_5")
        with open('./examples/with_preds/arbiter/program5.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_6(self):
        logging.info("Starting test_synthesize_6")
        with open('./examples/with_preds/arbiter/program6.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertFalse(real)

    def test_synthesize_7(self):
        logging.info("Starting test_synthesize_7")
        with open('./examples/with_preds/arbiter/program7.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_7_5(self):
        logging.info("Starting test_synthesize_7_5")
        with open('./examples/with_preds/arbiter/program7.5.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertFalse(real)

    def test_synthesize_8(self):
        logging.info("Starting test_synthesize_8")
        with open('./examples/with_preds/arbiter/program8.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertFalse(real)

    def test_synthesize_9(self):
        logging.info("Starting test_synthesize_9")
        with open('./examples/with_preds/arbiter/program9.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_10(self):
        logging.info("Starting test_synthesize_10")
        with open('./examples/with_preds/arbiter/program10.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

    def test_synthesize_11(self):
        logging.info("Starting test_synthesize_11")
        with open('./examples/with_preds/arbiter/program11.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertFalse(real)

    def test_road(self):
        with open('./examples/with_preds/arbiter/road.prog') as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None, True, False)
            self.assertTrue(real)

