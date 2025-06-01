import os
import time
from pathlib import Path
from unittest import TestCase

from parsing.string_to_program import string_to_program
from synthesis.synthesis import synthesize
import logging

logdir = Path(os.getcwd()) / "logs"

if not os.path.exists(logdir):
    os.makedirs(logdir)

os.environ["PATH"] = "../binaries:" + os.environ["PATH"]

logging.basicConfig(
    filename=str(logdir) + "/tests" + str(time.time()) + ".log",
    encoding="utf-8",
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)


class Test(TestCase):

    def setUp(self):
        os.environ["PATH"] = "../binaries:" + os.environ["PATH"]
        os.environ["PATH"] = "./binaries:" + os.environ["PATH"]

    def test_synthesize_1(self):
        logging.info("Starting test_synthesize_1")
        with open("./test-problems/program.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_2(self):
        logging.info("Starting test_synthesize_2")
        with open("./test-problems/program2.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_3(self):
        logging.info("Starting test_synthesize_3")
        with open("./test-problems/program3.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertFalse(real)

    def test_synthesize_4(self):
        logging.info("Starting test_synthesize_4")
        with open("./test-problems/program4.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_5(self):
        logging.info("Starting test_synthesize_5")
        with open("./test-problems/program5.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_6(self):
        logging.info("Starting test_synthesize_6")
        with open("./test-problems/program6.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertFalse(real)

    def test_synthesize_7(self):
        logging.info("Starting test_synthesize_7")
        with open("./test-problems/program7.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            self.assertTrue(not program.deterministic)

    def test_synthesize_7_5(self):
        logging.info("Starting test_synthesize_7_5")
        with open("./test-problems/program7.5.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertFalse(real)

    def test_synthesize_8(self):
        logging.info("Starting test_synthesize_8")
        with open("./test-problems/program8.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertFalse(real)

    def test_synthesize_9(self):
        logging.info("Starting test_synthesize_9")
        with open("./test-problems/program9.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_10(self):
        logging.info("Starting test_synthesize_10")
        with open("./test-problems/program10.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)

    def test_synthesize_11(self):
        logging.info("Starting test_synthesize_11")
        with open("./test-problems/program11.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertFalse(real)

    def test_road(self):
        with open("./test-problems/road.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            (real, mm) = synthesize(program, ltl_spec, None)
            self.assertTrue(real)
