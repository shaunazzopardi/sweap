import csv
from contextlib import contextmanager, nullcontext, redirect_stdout, redirect_stderr
from io import StringIO
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from benchmarks.scripts.python import run_benchmarks as runner


class FakeRuntime:
    environment = staticmethod(nullcontext)

    def __init__(self, parsed=None, solved=None, verified=None):
        self.parsed = list(parsed or [])
        self.solved = list(solved or [])
        self.verified = list(verified or [])
        self.calls = []

    def reset(self):
        pass

    @contextmanager
    def configured(self, settings, source, log, dual):
        self.dual = dual
        self.settings = settings
        yield

    def parse(self, source, settings):
        self.calls.append(("parse", source.name, self.dual))
        return self.parsed.pop(0) if self.parsed else (True, ("program", "objective"))

    def solve(self, program, objective, settings):
        self.calls.append(("solve", program, self.dual))
        return self.solved.pop(0) if self.solved else (True, SimpleNamespace(realisable=True))

    def verify(self, program, objective, hoa, settings):
        self.calls.append(("verify", program, self.dual))
        return self.verified.pop(0) if self.verified else (True, True)


class TestBenchmarkRunner(TestCase):
    def setUp(self):
        self.temporary = TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.output = self.root / "results.csv"
        self.capture = redirect_stdout(StringIO())
        self.capture.__enter__()
        self.addCleanup(self.capture.__exit__, None, None, None)

    def source(self, key):
        path = self.root / "inputs" / key
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()
        return path

    def invoke(self, *args, runtime=None):
        runtime = runtime or FakeRuntime()
        with patch.object(runner, "Runtime", return_value=runtime):
            status = runner.main(list(args))
        self.assertEqual(status, 0)
        return runtime

    def rows(self):
        with self.output.open(newline="") as stream:
            return list(csv.DictReader(stream))

    def test_generated_name_includes_dual_solver_and_parameters(self):
        self.source("case.prog")
        args = runner.parser().parse_args([
            "sweap", "--input", str(self.root / "inputs"), "--dual", "--backend", "strix",
            "--workers", "3", "--memory-gb", "7", "--no-verify", "--lazy",
        ])
        settings = runner.resolve_settings(args)
        name = runner.output_name(settings)
        self.assertRegex(name, r"^\d{8}T\d{12}Z-sweap-dstrix-")
        for tag in ("p10", "s20", "m7", "w3", "noverify", "lazy"):
            self.assertIn(tag, name)

    def test_resume_restores_settings_and_keeps_equal_basenames_distinct(self):
        self.source("a/same.prog")
        self.source("b/same.prog")
        self.invoke("sweap", "--input", str(self.root / "inputs"), "--output", str(self.output),
                    "--dual", "--backend", "strix", "--limit", "1")
        self.assertEqual([r["file"] for r in self.rows()], ["a/same.prog"])
        resumed = self.invoke("--resume", str(self.output))
        self.assertEqual(resumed.settings["backend"], "strix")
        self.assertTrue(resumed.settings["dual"])
        self.assertEqual([r["file"] for r in self.rows()], ["a/same.prog", "b/same.prog"])
        with patch.object(runner, "Runtime") as runtime:
            self.assertEqual(runner.main(["--resume", str(self.output)]), 0)
            runtime.assert_not_called()

    def test_resume_rejects_changed_run_settings_without_modifying_csv(self):
        self.source("case.prog")
        self.invoke("sweap", "--input", str(self.root / "inputs"), "--output", str(self.output), "--dual")
        before = self.output.read_bytes()
        with redirect_stderr(StringIO()), self.assertRaises(SystemExit) as error:
            runner.main(["--resume", str(self.output), "--no-dual"])
        self.assertEqual(error.exception.code, 2)
        self.assertEqual(self.output.read_bytes(), before)

    def test_output_never_silently_resumes_or_overwrites(self):
        self.source("case.prog")
        self.output.write_text("keep me\n")
        with redirect_stderr(StringIO()), self.assertRaises(SystemExit):
            runner.main(["sweap", "--input", str(self.root / "inputs"), "--output", str(self.output)])
        self.assertEqual(self.output.read_text(), "keep me\n")

    def test_resume_legacy_csv_preserves_columns_and_adds_verification(self):
        self.source("a/old.prog")
        self.source("b/new.prog")
        self.output.write_text("file,realisable,note\nold.prog,True,keep this\n")
        self.invoke("sweap", "--input", str(self.root / "inputs"), "--resume", str(self.output))
        rows = self.rows()
        self.assertEqual(rows[0]["note"], "keep this")
        self.assertEqual(rows[1]["file"], "b/new.prog")
        self.assertEqual(rows[1]["verification"], "True")
        self.assertEqual(len(rows), 2)

    def test_legacy_verification_column_is_retained(self):
        self.source("new.prog")
        self.output.write_text("file,realisable,verification_10s\nold.prog,False,TO\n")
        self.invoke("sweap", "--input", str(self.root / "inputs"), "--resume", str(self.output))
        self.assertEqual(self.rows()[0]["verification_10s"], "TO")
        self.assertEqual(self.rows()[1]["verification_10s"], "True")

    def test_ambiguous_legacy_basename_is_rejected_even_with_include_filter(self):
        self.source("a/same.prog")
        self.source("b/same.prog")
        self.output.write_text("file,realisable\nsame.prog,True\n")
        with redirect_stderr(StringIO()), self.assertRaises(SystemExit):
            runner.main(["sweap", "--input", str(self.root / "inputs"), "--resume", str(self.output), "--include", "a/*"])
        self.assertFalse(runner.metadata_path(self.output).exists())

    def test_list_does_not_create_results(self):
        self.source("case.issy")
        self.invoke("issy", "--input", str(self.root / "inputs"), "--list")
        self.assertFalse((self.root / "inputs/results").exists())

    def test_discovery_includes_tsl_suffixes_and_excludes_artifacts(self):
        for key in ("a.tsl", "b.tslmt", "c.tslt", "logs/skip.tsl", "results/skip.tsl", "skip.issy"):
            self.source(key)
        cases = runner.discover({"format": "tsl", "input": str(self.root / "inputs")})
        self.assertEqual(list(cases), ["a.tsl", "b.tslmt", "c.tslt"])

    def test_dual_retry_reparses_and_verifies_the_retry_program(self):
        runtime = FakeRuntime(parsed=[(True, ("first", "ltl")), (True, ("second", "ltl2"))],
                              solved=[(False, "Timeout"), (True, SimpleNamespace(realisable=False))])
        settings = dict(runner.DEFAULTS, dual_fallback=True)
        row = runner.run_case(self.source("case.prog"), "case.prog", settings, self.root, runtime)
        self.assertEqual(row["realisable"], "False (dual-alt)")
        self.assertEqual(runtime.calls, [("parse", "case.prog", False), ("solve", "first", False),
                                         ("parse", "case.prog", True), ("solve", "second", True),
                                         ("verify", "second", True)])

    def test_parse_retry_failure_is_distinct_from_synthesis_failure(self):
        runtime = FakeRuntime(parsed=[(True, ("p", "ltl")), (False, "Memory limit exceeded")],
                              solved=[(False, "Timeout")])
        row = runner.run_case(self.source("case.prog"), "case.prog", dict(runner.DEFAULTS, dual_fallback=True), self.root, runtime)
        self.assertEqual(row["realisable"], "OOM(parse-dual-alt)")
        self.assertEqual(sum(c[0] == "solve" for c in runtime.calls), 1)

    def test_success_never_retries_and_verification_can_be_disabled(self):
        runtime = FakeRuntime()
        settings = dict(runner.DEFAULTS, dual_fallback=True, verify=False)
        row = runner.run_case(self.source("case.prog"), "case.prog", settings, self.root, runtime)
        self.assertIs(row["realisable"], True)
        self.assertEqual(row["verification"], "N/A")
        self.assertEqual([c[0] for c in runtime.calls], ["parse", "solve"])

    def test_verification_failure_does_not_change_synthesis_verdict(self):
        runtime = FakeRuntime(verified=[(False, "controller does not enforce the required LTL property")])
        row = runner.run_case(self.source("case.prog"), "case.prog", dict(runner.DEFAULTS), self.root, runtime)
        self.assertIs(row["realisable"], True)
        self.assertIs(row["verification"], False)

    def test_invalid_limits_and_incompatible_flags_are_rejected(self):
        for flags in (["--workers", "0"], ["--parse-timeout", "0"], ["--memory-gb", "nan"],
                      ["--synthesis-memory-limit-mb", "0"], ["--finite", "--no-binary-enc"]):
            with self.subTest(flags=flags), self.assertRaises(ValueError):
                runner.resolve_settings(runner.parser().parse_args(["sweap", *flags]))

    def test_configuration_is_restored_after_an_attempt_raises(self):
        import config
        runtime = runner.Runtime.__new__(runner.Runtime)
        runtime.conf = config.Config.getConfig()
        before = {key: getattr(runtime.conf, key) for key in
                  ("dual", "backend", "workers", "verify_controller", "name", "log")}
        settings = dict(runner.DEFAULTS, format="sweap", backend="strix", workers=3)
        with self.assertRaisesRegex(RuntimeError, "attempt failed"):
            with runtime.configured(settings, self.source("case.prog"), self.root, True):
                self.assertTrue(runtime.conf.dual)
                self.assertEqual(runtime.conf.backend, "strix")
                self.assertEqual(runtime.conf.workers, 3)
                raise RuntimeError("attempt failed")
        self.assertEqual({key: getattr(runtime.conf, key) for key in before}, before)

    def test_solver_cleanup_runs_even_when_the_process_wrapper_raises(self):
        runtime = runner.Runtime.__new__(runner.Runtime)
        runtime.synthesize = object()
        runtime.run_limited = lambda *args: (_ for _ in ()).throw(RuntimeError("failed"))
        with patch.object(runner, "kill_solver_processes") as cleanup:
            with self.assertRaises(RuntimeError):
                runtime.solve("program", "objective", runner.DEFAULTS)
            cleanup.assert_called_once_with()

    def test_verification_exception_preserves_the_synthesis_verdict(self):
        runtime = FakeRuntime()
        with patch.object(runtime, "verify", side_effect=RuntimeError("verification process failed")):
            row = runner.run_case(self.source("case.prog"), "case.prog", dict(runner.DEFAULTS), self.root, runtime)
        self.assertIs(row["realisable"], True)
        self.assertEqual(row["verification"], "ERR(verif): verification process failed")
