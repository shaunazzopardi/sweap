import json
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from benchmarks.scripts.python import run_all_benchmarks as runner


class TestRunAllBenchmarks(TestCase):
    def setUp(self):
        temporary = TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        results = patch.object(runner, "RESULTS", self.root)
        results.start()
        self.addCleanup(results.stop)

    def csv(self, directory, name, kind, dual):
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / name
        path.write_text("file,realisable\nfinished.prog,True\n")
        path.with_suffix(".csv.json").write_text(json.dumps({
            "settings": {"format": kind, "dual": dual},
        }))
        return path

    def invoke(self, *args):
        with (
            patch("sys.argv", ["run_all_benchmarks.py", *map(str, args)]),
            patch.object(runner.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run,
            redirect_stdout(StringIO()),
        ):
            self.assertEqual(0, runner.main())
        return [call.args[0] for call in run.call_args_list]

    def test_resume_latest_batch_uses_timestamp_not_unrelated_directories(self):
        old = self.root / "20261101T120000000000Z"
        latest = self.root / "20261102T120000000000Z"
        self.csv(old, "old.csv", "sweap", False)
        saved = self.csv(latest, "latest.csv", "sweap", False)
        (self.root / "unrelated-directory").mkdir()
        commands = self.invoke("--resume")
        self.assertEqual(8, len(commands))
        self.assertEqual(str(saved), commands[0][commands[0].index("--resume") + 1])
        self.assertTrue(all(str(latest) in command for command in commands[1:]))

    def test_resume_partial_batch_starts_only_missing_configurations(self):
        batch = self.root / "custom-batch"
        normal = self.csv(batch, "opaque-a.csv", "sweap", False)
        dual = self.csv(batch, "opaque-b.csv", "issy", True)
        original = {p: p.read_bytes() for p in batch.iterdir()}
        commands = self.invoke("--resume", batch)
        resumed = [command for command in commands if "--resume" in command]
        self.assertEqual(2, len(resumed))
        self.assertIn(str(normal), resumed[0])
        self.assertIn(str(dual), resumed[1])
        self.assertNotIn("--dual", resumed[0])
        self.assertIn("--dual", resumed[1])
        self.assertEqual(6, sum("--output-dir" in command for command in commands))
        self.assertEqual(original, {p: p.read_bytes() for p in batch.iterdir()})

    def test_resume_complete_batch_resumes_all_eight_csvs(self):
        batch = self.root / "complete"
        for dual in (False, True):
            for kind in runner.FORMATS:
                self.csv(batch, f"{kind}-{dual}.csv", kind, dual)
        commands = self.invoke("--resume", batch)
        self.assertEqual(8, len(commands))
        self.assertTrue(all("--resume" in command for command in commands))
        self.assertFalse(any("--output-dir" in command for command in commands))
        self.assertEqual(4, sum("--dual" in command for command in commands))

    def test_without_resume_creates_a_new_batch(self):
        previous = self.root / "20261101T120000000000Z"
        self.csv(previous, "old.csv", "sweap", False)
        commands = self.invoke()
        directory = Path(commands[0][commands[0].index("--output-dir") + 1])
        self.assertEqual(self.root, directory.parent)
        self.assertNotEqual(previous, directory)
        self.assertFalse(any("--resume" in command for command in commands))

    def test_missing_previous_batch_fails_before_running_anything(self):
        with (
            patch("sys.argv", ["run_all_benchmarks.py", "--resume"]),
            patch.object(runner.subprocess, "run") as run,
            redirect_stderr(StringIO()),
        ):
            with self.assertRaises(SystemExit) as error:
                runner.main()
            self.assertEqual(2, error.exception.code)
            run.assert_not_called()

    def test_ambiguous_csvs_fail_before_running_anything(self):
        batch = self.root / "ambiguous"
        self.csv(batch, "first.csv", "sweap", False)
        self.csv(batch, "second.csv", "sweap", False)
        with (
            patch("sys.argv", ["run_all_benchmarks.py", "--resume", str(batch)]),
            patch.object(runner.subprocess, "run") as run,
            redirect_stderr(StringIO()),
        ):
            with self.assertRaises(SystemExit) as error:
                runner.main()
            self.assertEqual(2, error.exception.code)
            run.assert_not_called()
