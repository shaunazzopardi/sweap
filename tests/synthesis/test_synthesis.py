import inspect
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from unittest import TestCase
from unittest.mock import patch

from pysmt.shortcuts import get_env

import config
import programs.util
from parsing.string_to_program import string_to_program
from programs.util import reset_caches
from synthesis.synthesis import synthesize
import logging
import sys
import functools

REPO = Path(__file__).resolve().parents[2]
PROBLEMS = REPO / "tests" / "test-problems"
logdir = REPO / "tests" / "logs"

if not os.path.exists(logdir):
    os.makedirs(logdir)

logging.basicConfig(
    filename=str(logdir) + "/tests" + str(time.time()) + ".log",
    encoding="utf-8",
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)


class Test(TestCase):

    def setUp(self):
        env = patch.dict(os.environ, {
            "PATH": str(REPO / "binaries") + os.pathsep + os.environ.get("PATH", "")
        })
        env.start()
        self.addCleanup(env.stop)
        conf = config.Config.getConfig()
        self.addCleanup(setattr, conf, "debug", conf.debug)
        self.addCleanup(setattr, conf, "workers", conf.workers)
        self.addCleanup(reset_caches)
        self.addCleanup(programs.util.reset_caches)
        conf.debug = True
        conf.workers = 1

    def assert_nondeterministic_program_rejected(self, filename):
        with self.assertRaisesRegex(
            Exception, "Found non-deterministic transitions with overlapping guards:"
        ):
            string_to_program((PROBLEMS / filename).read_text())

    def require_java17(self):
        java = os.environ.get("JAVA") or shutil.which("java")
        if not java:
            self.skipTest("CPAchecker requires Java 17 or newer (set JAVA or PATH)")
        try:
            result = subprocess.run(
                [java, "-XX:-UsePerfData", "-Xmx5m", "-version"],
                capture_output=True, text=True, timeout=5,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            self.skipTest(f"CPAchecker cannot run Java at {java}: {error}")
        match = re.search(r'version "(\d+)', result.stdout + result.stderr)
        if result.returncode != 0 or not match or int(match.group(1)) < 17:
            self.skipTest(f"CPAchecker requires a working Java 17+ runtime: {java}")

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
        with open(PROBLEMS / "program.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_2(self):
        logging.info("Starting test_synthesize_2")
        with open(PROBLEMS / "program2.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_synthesize_3(self):
        logging.info("Starting test_synthesize_3")
        with open(PROBLEMS / "program3.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_synthesize_4(self):
        logging.info("Starting test_synthesize_4")
        with open(PROBLEMS / "program4.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_program5_rejects_overlapping_guards(self):
        config.Config.getConfig().debug = False
        self.assert_nondeterministic_program_rejected("program5.prog")

    def test_program6_rejects_overlapping_guards(self):
        self.assert_nondeterministic_program_rejected("program6.prog")

    def test_program7_rejects_overlapping_guards(self):
        self.assert_nondeterministic_program_rejected("program7.prog")

    def test_program7_5_rejects_overlapping_guards(self):
        self.assert_nondeterministic_program_rejected("program7.5.prog")

    def test_synthesize_8(self):
        logging.info("Starting test_synthesize_8")
        with open(PROBLEMS / "program8.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_synthesize_9(self):
        logging.info("Starting test_synthesize_9")
        with open(PROBLEMS / "program9.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)

    def test_program10_rejects_overlapping_guards(self):
        config.Config.getConfig().debug = False
        self.assert_nondeterministic_program_rejected("program10.prog")

    def test_synthesize_11(self):
        self.require_java17()
        if "bdd" not in get_env().factory.all_solvers():
            self.skipTest("program11 structural refinement requires the pySMT BDD backend")
        logging.info("Starting test_synthesize_11")
        with open(PROBLEMS / "program11.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertFalse(wrapped_hoa.realisable)

    def test_road(self):
        with open(PROBLEMS / "road.prog") as program_file:
            program, ltl_spec = string_to_program(program_file.read())
            wrapped_hoa = synthesize(program, ltl_spec, None)
            self.assertTrue(wrapped_hoa.realisable)
