import inspect
import os
import time
from pathlib import Path
from unittest import TestCase

import config
import programs.util
from parsing.string_to_program import string_to_program
from programs.util import reset_caches
from synthesis.synthesis import synthesize
import logging
import sys
import functools

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
        config.Config.getConfig().debug = True

    def tearDown(self):
        config.Config.getConfig().debug = False
        reset_caches()
        programs.util.reset_caches()

    def clear_module_lru_caches(self, names=None):
        """Clear @lru_cache decorated functions in specified modules"""
        if names is None:
            # Clear caches in prop_lang modules by default
            names = [
                "prop_lang.biop",
                "prop_lang.formula",
                "prop_lang.uniop",
                "prop_lang.value",
            ]

        cleared_count = 0

        for module_name in names:
            if module_name in sys.modules:
                module = sys.modules[module_name]

                # Iterate through all attributes in the module
                for attr_name in dir(module):
                    attr = getattr(module, attr_name)

                    # Check if it's an lru_cache decorated function
                    if isinstance(attr, functools._lru_cache_wrapper):
                        try:
                            attr.cache_clear()
                            cleared_count += 1
                            if config.Config.getConfig().debug:
                                print(f"Cleared cache for {module_name}.{attr_name}")
                        except Exception as e:
                            print(
                                f"Failed to clear cache for {module_name}.{attr_name}: {e}"
                            )

                    # Check for class methods with lru_cache
                    elif inspect.isclass(attr):
                        for method_name in dir(attr):
                            method = getattr(attr, method_name)
                            if isinstance(method, functools._lru_cache_wrapper):
                                try:
                                    method.cache_clear()
                                    cleared_count += 1
                                    if config.Config.getConfig().debug:
                                        print(
                                            f"Cleared cache for {module_name}.{attr_name}.{method_name}"
                                        )
                                except Exception as e:
                                    print(
                                        f"Failed to clear cache for {module_name}.{attr_name}.{method_name}: {e}"
                                    )

        return cleared_count

    def test_synthesize_1(self):
        logging.info("Starting test_synthesize_1")
        with open("./test-problems/program.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_2(self):
        logging.info("Starting test_synthesize_2")
        with open("./test-problems/program2.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_3(self):
        logging.info("Starting test_synthesize_3")
        with open("./test-problems/program3.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_synthesize_4(self):
        logging.info("Starting test_synthesize_4")
        with open("./test-problems/program4.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_5(self):
        logging.info("Starting test_synthesize_5")
        config.Config.getConfig().debug = False
        with open("./test-problems/program5.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_6(self):
        logging.info("Starting test_synthesize_6")
        with open("./test-problems/program6.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            with self.assertRaises(Exception):
                synthesize(program, ltl_spec, None)

    def test_synthesize_7(self):
        logging.info("Starting test_synthesize_7")
        with open("./test-problems/program7.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            self.assertTrue(not program.deterministic)

    def test_synthesize_7_5(self):
        logging.info("Starting test_synthesize_7_5")
        with open("./test-problems/program7.5.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            with self.assertRaises(Exception):
                synthesize(program, ltl_spec, None)

    def test_synthesize_8(self):
        logging.info("Starting test_synthesize_8")
        with open("./test-problems/program8.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_synthesize_9(self):
        logging.info("Starting test_synthesize_9")
        with open("./test-problems/program9.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_10(self):
        logging.info("Starting test_synthesize_10")
        config.Config.getConfig().debug = False
        with open("./test-problems/program10.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_11(self):
        logging.info("Starting test_synthesize_11")
        with open("./test-problems/program11.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_road(self):
        with open("./test-problems/road.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)
