from unittest import TestCase

from parsing.string_to_program import string_to_program
import os


class Test(TestCase):

    def test_infinite_benchmarks(self):
        for file in os.listdir("../benchmarks/sweap"):
            if file.endswith(".prog"):
                with open("../benchmarks/sweap/" + str(file)) as program_file:
                    print(str(file))
                    program, ltl_spec = string_to_program(program_file.read())

    def test_finite_benchmarks(self):
        for file in os.listdir("../benchmarks/sweap/finite"):
            if file.endswith(".prog"):
                with open("../benchmarks/sweap/finite/" + str(file)) as program_file:
                    print(str(file))
                    program, ltl_spec = string_to_program(program_file.read())
