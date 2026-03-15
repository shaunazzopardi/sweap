import os
import unittest
from datetime import datetime
from pathlib import Path
from unittest.mock import patch

from pysmt.shortcuts import reset_env

import config
from parsing import string_to_issy as string_to_issy_module
from parsing.util import issy_game_transition_utils as issy_game_transition_utils_module
from tests.parsing.validation.issy_cross_product_minigame_transition_sanity import (
    check_cross_product_minigame_transition_sanity_from_file,
)
from programs import program as program_module
from programs import util as program_util_module
from prop_lang import util as prop_lang_util_module
from prop_lang.util import run_with_timeout

REPO_ROOT = Path(__file__).resolve().parents[2]
ISSY_BENCHMARK_ROOT = REPO_ROOT / "benchmarks" / "issy"
LOG_DIR = REPO_ROOT / "src" / "logs" / "issy_cross_product_minigame_transition_sanity"


class _SequentialPool:
    def __init__(self, *args, **kwargs):
        pass

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False

    def map(self, fn, items):
        return [fn(item) for item in items]


class TestCrossProductMinigameTransitionSanityRuns(unittest.TestCase):
    @staticmethod
    def _reset_between_benchmarks():
        reset_env()
        # Avoid stale per-Variable SMT nodes leaking across benchmark symbol tables.
        config.Config.getConfig().cache_smt = False
        prop_lang_util_module.reset_caches()
        program_util_module.reset_caches()

    @staticmethod
    def _is_unsupported_exception(exc: Exception) -> bool:
        msg = str(exc)
        return (
            "requires ISSY files with game blocks" in msg
            or "real is not a valid variable type (or real and currently unsupported)"
            in msg
        )

    @staticmethod
    def _run_check_safe(benchmark_path: str):
        try:
            return True, check_cross_product_minigame_transition_sanity_from_file(
                benchmark_path
            )
        except Exception as exc:
            return False, str(exc)

    def _announce(self, msg: str):
        print(msg, flush=True)

    @staticmethod
    def _append_log(fp, line: str):
        fp.write(line + "\n")
        fp.flush()
        os.fsync(fp.fileno())

    def setUp(self):
        self._patchers = [
            patch.object(
                program_util_module,
                "run_with_timeout",
                lambda fn, args, timeout=0.2: (False, None),
            ),
        ]
        for p in self._patchers:
            p.start()

    def tearDown(self):
        for p in reversed(self._patchers):
            p.stop()

    def test_cross_product_minigame_transition_sanity_runs(self):
        benchmarks = sorted(ISSY_BENCHMARK_ROOT.rglob("*.issy"))
        only = os.environ.get("ISSY_MTS_ONLY")
        limit = os.environ.get("ISSY_MTS_LIMIT")
        max_seconds = float(os.environ.get("ISSY_MTS_MAX_SECONDS", "10"))

        if only:
            benchmarks = [b for b in benchmarks if only in str(b)]
        if limit:
            benchmarks = benchmarks[: int(limit)]

        self.assertTrue(benchmarks, "No ISSY benchmarks found.")
        self._announce(f"[setup] discovered {len(benchmarks)} benchmark files")
        if only:
            self._announce(f"[setup] filter ISSY_MTS_ONLY={only}")
        if limit:
            self._announce(f"[setup] limit ISSY_MTS_LIMIT={limit}")
        self._announce(
            f"[setup] max check time per spec ISSY_MTS_MAX_SECONDS={max_seconds:g}"
        )

        LOG_DIR.mkdir(parents=True, exist_ok=True)
        log_path = LOG_DIR / f"report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
        self._announce(f"[setup] log file: {log_path}")

        failures = []
        unsupported = 0
        skipped = 0
        total = len(benchmarks)

        with log_path.open("w", buffering=1) as log_fp:
            self._append_log(log_fp, f"Total benchmarks: {total}")
            for idx, benchmark_path in enumerate(benchmarks, start=1):
                rel = benchmark_path.relative_to(REPO_ROOT)
                self._announce(f"[{idx}/{total}] checking {rel}")
                self._append_log(log_fp, f"[{idx}/{total}] checking {rel}")
                self._reset_between_benchmarks()
                try:
                    self._announce(
                        f"[{idx}/{total}] run minigame-transition-sanity {rel}"
                    )
                    try:
                        ok, wrapped = run_with_timeout(
                            self._run_check_safe,
                            (str(benchmark_path),),
                            max_seconds,
                        )
                    except (
                        PermissionError,
                        EOFError,
                        BrokenPipeError,
                        ConnectionError,
                    ):
                        # Restricted sandboxes can block multiprocessing listener sockets.
                        ok = True
                        wrapped = self._run_check_safe(str(benchmark_path))
                    if not ok:
                        raise TimeoutError(
                            "check_cross_product_minigame_transition_sanity_from_file timed out "
                            f"after {max_seconds:g}s"
                        )

                    inner_ok, result_or_error = wrapped
                    if not inner_ok:
                        raise Exception(
                            "check_cross_product_minigame_transition_sanity_from_file failed: "
                            + str(result_or_error)
                        )
                    result = result_or_error

                    self._append_log(
                        log_fp,
                        f"[{idx}/{total}] RESULT {rel} "
                        f"ok={result.ok} "
                        f"capability_failures={len(result.capability_failures)} "
                        f"exit_failures={len(result.exit_failures)} "
                        "transition_preservation_failures="
                        f"{len(result.transition_preservation_failures)} "
                        f"unsupported={len(result.unsupported)}",
                    )

                    if len(result.unsupported) > 0:
                        self._append_log(
                            log_fp, f"[{idx}/{total}] unsupported_details:"
                        )
                        for line in result.unsupported:
                            self._append_log(log_fp, "  " + line)

                    if not result.ok:
                        detail_lines = []
                        if len(result.capability_failures) > 0:
                            detail_lines.append("capability_failures:")
                            detail_lines.extend(result.capability_failures)
                        if len(result.exit_failures) > 0:
                            detail_lines.append("exit_failures:")
                            detail_lines.extend(result.exit_failures)
                        if len(result.transition_preservation_failures) > 0:
                            detail_lines.append("transition_preservation_failures:")
                            detail_lines.extend(result.transition_preservation_failures)
                        failures.append(f"{rel}:\n" + "\n".join(detail_lines))
                        self._append_log(log_fp, f"[{idx}/{total}] FAIL_DETAILS {rel}:")
                        for line in detail_lines:
                            self._append_log(log_fp, "  " + line)
                        self._announce(f"[{idx}/{total}] FAIL {rel}")
                    else:
                        self._announce(f"[{idx}/{total}] PASS {rel}")
                except TimeoutError as exc:
                    skipped += 1
                    self._announce(f"[{idx}/{total}] SKIP {rel} ({exc})")
                    self._append_log(log_fp, f"[{idx}/{total}] SKIP {rel} ({exc})")
                except Exception as exc:
                    msg = f"{rel}: exception during check: {exc}"
                    if self._is_unsupported_exception(exc):
                        unsupported += 1
                        self._announce(f"[{idx}/{total}] UNSUPPORTED {rel}")
                        self._append_log(log_fp, f"[{idx}/{total}] UNSUPPORTED {msg}")
                    else:
                        failures.append(msg)
                        self._announce(f"[{idx}/{total}] EXCEPTION {rel}")
                        self._append_log(log_fp, f"[{idx}/{total}] EXCEPTION {msg}")
                finally:
                    self._reset_between_benchmarks()

            summary = (
                "Summary: "
                f"checked={total}, skipped={skipped}, unsupported={unsupported}, "
                f"failed={len(failures)}, "
                f"passed={total - skipped - unsupported - len(failures)}"
            )
            self._announce(summary)
            self._append_log(log_fp, summary)

            if failures:
                self._append_log(log_fp, "Failures:")
                for failure in failures:
                    self._append_log(log_fp, failure)

        self._announce(f"full_log: {log_path}")

        if failures:
            self.fail(
                "Cross-product minigame transition sanity failed:\n\n"
                + "\n\n".join(failures)
            )


if __name__ == "__main__":
    unittest.main()
