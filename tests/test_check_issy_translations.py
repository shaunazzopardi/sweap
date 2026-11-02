import importlib.util
import csv
from threading import Barrier
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "benchmarks/scripts/python/check_issy_translations.py"
SPEC = importlib.util.spec_from_file_location("check_issy_translations", SCRIPT)
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class TestIssyTranslationRunner(TestCase):
    def test_discovery_formats_filters_and_excluded_artifacts(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ("a.prog", "b.issy", "c.tslmt", "d.tslt", "e.rpg", "logs/f.issy", "results/g.prog"):
                path = root / name
                path.parent.mkdir(exist_ok=True)
                path.touch()
            selected = runner.discover([root, root / "a.prog"], set(runner.INPUT_FLAGS), [])
            self.assertEqual([p.name for p in selected], ["a.prog", "b.issy", "c.tslmt", "d.tslt", "e.rpg"])
            self.assertEqual(
                [p.name for p in runner.discover([root], {"issy"}, ["*/b.issy"])],
                ["b.issy"],
            )

    def test_verdict_requires_success_and_unambiguous_standalone_output(self):
        with TemporaryDirectory() as temporary:
            path = Path(temporary) / "stdout"
            result = {"status": "pass", "stdout": str(path)}
            for text, expected in (
                ("Unrealizable\n", "unrealizable"),
                ("Realizable\n", "realizable"),
                ("warning: Realizable?\n", None),
                ("Realizable\nUnrealizable\n", None),
            ):
                path.write_text(text)
                self.assertEqual(runner.verdict(result), expected)
            path.write_text("Realizable\n")
            self.assertIsNone(runner.verdict(dict(result, status="timeout")))
            self.assertIsNone(runner.verdict(dict(result, status="error")))

    def test_stage_timeout_and_nonzero_exit(self):
        with TemporaryDirectory() as temporary:
            directory = Path(temporary)
            result = runner.run_stage(
                [sys.executable, "-c", "import time; time.sleep(5)"],
                directory, "slow", 0.1,
            )
            self.assertEqual(result["status"], "timeout")
            result = runner.run_stage(
                [sys.executable, "-c", "print('Realizable'); raise SystemExit(3)"],
                directory, "failed", 2,
            )
            self.assertEqual(result["status"], "error")
            self.assertEqual(result["returncode"], 3)
            self.assertIsNone(runner.verdict(result))

    def test_comparisons_do_not_treat_failures_as_matching_verdicts(self):
        for original, translated, status, expected in (
            ("Realizable", "Realizable", "pass", "match"),
            ("Realizable", "Unrealizable", "pass", "mismatch"),
            ("Realizable", "Realizable", "timeout", "inconclusive"),
            ("", "", "pass", "inconclusive"),
        ):
            with self.subTest(expected=expected), TemporaryDirectory() as temporary:
                root = Path(temporary)
                source = root / "source.issy"
                source.touch()
                args = SimpleNamespace(
                    workers=1, translation_timeout=1, acceptance_timeout=1,
                    solve_timeout=1, acceptance="to-game", skip_verdicts=False,
                )

                def stage(command, directory, name, timeout):
                    if name == "translation":
                        (directory / "translated.issy").touch()
                    output = directory / (name + ".stdout.log")
                    output.write_text(
                        original if name == "original_solve" else
                        translated if name == "translated_solve" else ""
                    )
                    return {
                        "status": status if name == "original_solve" else "pass",
                        "stdout": str(output),
                    }

                with patch.object(runner, "run_stage", side_effect=stage):
                    record = runner.check_case(source, root / "case", args, ["issy"])
                self.assertEqual(record["summary"]["comparison"], expected)
                self.assertTrue((root / "case/result.json").is_file())

    def test_parallel_cases_keep_all_results(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ("a.issy", "b.issy"):
                (root / name).touch()
            barrier = Barrier(2)

            def check(source, directory, args, command):
                barrier.wait(timeout=5)
                return {"summary": {"file": source.name, "translation": "pass", "acceptance": "pass",
                                    "comparison": "match"}}

            output = root / "output"
            argv = [str(SCRIPT), "--root", str(root), "--jobs", "2",
                    "--issy", sys.executable, "--output", str(output)]
            with patch.object(sys, "argv", argv), patch.object(
                runner, "check_case", side_effect=check
            ), patch.dict(runner.os.environ):
                self.assertEqual(runner.main(), 0)
            with (output / "results.csv").open() as stream:
                self.assertEqual({r["file"] for r in csv.DictReader(stream)},
                                 {"a.issy", "b.issy"})
