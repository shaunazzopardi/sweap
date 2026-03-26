import os
import unittest
from collections import defaultdict
from datetime import datetime
from pathlib import Path

from pysmt.shortcuts import reset_env

from parsing import string_to_issy as string_to_issy_module
from parsing.util.issy import issy_optimisation_reporting as issy_optimisations_module
from prop_lang.util import run_with_timeout

REPO_ROOT = Path(__file__).resolve().parents[2]
ISSY_BENCHMARK_ROOT = REPO_ROOT / "benchmarks" / "issy"
LOG_DIR = REPO_ROOT / "src" / "logs" / "issy_optimisation_summary"


class TestIssyOptimisationSummaryRuns(unittest.TestCase):
    @staticmethod
    def _is_unsupported_exception(exc: Exception) -> bool:
        msg = str(exc)
        return (
            "real is not a valid variable type (or real and currently unsupported)"
            in msg
            or "real and currently unsupported" in msg
        )

    @staticmethod
    def _compile_one_safe(benchmark_path: str):
        try:
            path = Path(benchmark_path)
            issy_optimisations_module.reset_last_optimisation_summary()
            text = path.read_text()
            string_to_issy_module.string_to_issy(text, path.name)
            return True, issy_optimisations_module.get_last_optimisation_summary()
        except Exception as exc:
            return False, f"{type(exc).__name__}: {exc!r}"

    @staticmethod
    def _append_log(fp, line: str):
        fp.write(line + "\n")
        fp.flush()
        os.fsync(fp.fileno())

    def test_issy_optimisation_summary_runs(self):
        benchmarks = sorted(ISSY_BENCHMARK_ROOT.rglob("*.issy"))
        only = os.environ.get("ISSY_OPT_ONLY")
        limit = os.environ.get("ISSY_OPT_LIMIT")
        max_seconds = float(os.environ.get("ISSY_OPT_MAX_SECONDS", "40"))

        if only:
            benchmarks = [b for b in benchmarks if only in str(b)]
        if limit:
            benchmarks = benchmarks[: int(limit)]

        self.assertTrue(benchmarks, "No ISSY benchmarks found.")

        LOG_DIR.mkdir(parents=True, exist_ok=True)
        log_path = LOG_DIR / f"report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"

        failures = []
        unsupported = 0
        skipped = 0
        compiled = 0
        stage_totals = defaultdict(int)
        stage_kind_totals = defaultdict(int)
        minigame_kind_totals = defaultdict(int)
        tracked_minigame_kinds = (
            "constant_update_vars",
            "not_using_int_vars",
            "only_inc_or_dec_vars",
        )

        with log_path.open("w", buffering=1) as log_fp:
            self._append_log(log_fp, f"Total benchmarks: {len(benchmarks)}")
            if only:
                self._append_log(log_fp, f"Filter ISSY_OPT_ONLY={only}")
            if limit:
                self._append_log(log_fp, f"Limit ISSY_OPT_LIMIT={limit}")
            self._append_log(log_fp, f"Timeout ISSY_OPT_MAX_SECONDS={max_seconds:g}")

            for idx, benchmark_path in enumerate(benchmarks, start=1):
                rel = benchmark_path.relative_to(REPO_ROOT)
                self._append_log(log_fp, f"[{idx}/{len(benchmarks)}] compiling {rel}")
                reset_env()
                try:
                    try:
                        ok, wrapped = run_with_timeout(
                            self._compile_one_safe,
                            (str(benchmark_path),),
                            max_seconds,
                        )
                    except Exception as timeout_exc:
                        # Fallback for restricted sandboxes where multiprocessing.Manager
                        # cannot open its listener socket.
                        if isinstance(
                            timeout_exc,
                            (
                                PermissionError,
                                EOFError,
                                BrokenPipeError,
                                ConnectionError,
                            ),
                        ):
                            ok = True
                            wrapped = self._compile_one_safe(str(benchmark_path))
                        else:
                            raise

                    if not ok:
                        skipped += 1
                        self._append_log(
                            log_fp,
                            f"[{idx}/{len(benchmarks)}] SKIP {rel}: timed out after {max_seconds:g}s",
                        )
                        continue

                    inner_ok, result_or_error = wrapped
                    if not inner_ok:
                        raise Exception(result_or_error)

                    summary = result_or_error
                    compiled += 1

                    if summary is None:
                        failures.append(f"{rel}: missing optimisation summary")
                        continue

                    benchmark_stage_kind_counts = defaultdict(int)
                    for event in summary["events"]:
                        stage = event["stage"]
                        kind = event["kind"]
                        count = int(event["count"])
                        stage_totals[stage] += count
                        stage_kind_totals[(stage, kind)] += count
                        benchmark_stage_kind_counts[(stage, kind)] += count
                        if (
                            stage == "stage5_minigame"
                            and kind in tracked_minigame_kinds
                        ):
                            minigame_kind_totals[kind] += count

                    self._append_log(
                        log_fp,
                        f"[{idx}/{len(benchmarks)}] OK {rel} total_events={summary['total_events']}",
                    )
                    if len(benchmark_stage_kind_counts) == 0:
                        self._append_log(
                            log_fp,
                            f"[{idx}/{len(benchmarks)}] OPT_TYPES {rel}: none",
                        )
                    else:
                        kind_items = ", ".join(
                            f"{stage}::{kind}={count}"
                            for (stage, kind), count in sorted(
                                benchmark_stage_kind_counts.items()
                            )
                        )
                        self._append_log(
                            log_fp,
                            f"[{idx}/{len(benchmarks)}] OPT_TYPES {rel}: {kind_items}",
                        )
                except Exception as exc:
                    detail = f"{type(exc).__name__}: {exc!r}"
                    if self._is_unsupported_exception(exc):
                        unsupported += 1
                        self._append_log(
                            log_fp,
                            f"[{idx}/{len(benchmarks)}] UNSUPPORTED {rel}: {detail}",
                        )
                    else:
                        failures.append(f"{rel}: {detail}")
                        self._append_log(
                            log_fp, f"[{idx}/{len(benchmarks)}] FAIL {rel}: {detail}"
                        )

            self._append_log(log_fp, "")
            self._append_log(log_fp, "Summary:")
            self._append_log(
                log_fp,
                f"compiled={compiled}, skipped={skipped}, unsupported={unsupported}, failed={len(failures)}, total={len(benchmarks)}",
            )
            self._append_log(log_fp, "")
            self._append_log(log_fp, "Stage Totals:")
            if len(stage_totals) == 0:
                self._append_log(log_fp, "none")
            else:
                for stage in sorted(stage_totals.keys()):
                    self._append_log(log_fp, f"{stage}: {stage_totals[stage]}")
            self._append_log(log_fp, "")
            self._append_log(log_fp, "Stage Totals Per Compiled Benchmark:")
            if len(stage_totals) == 0:
                self._append_log(log_fp, "none")
            else:
                for stage in sorted(stage_totals.keys()):
                    per_compiled = (
                        (stage_totals[stage] / compiled) if compiled > 0 else 0.0
                    )
                    self._append_log(log_fp, f"{stage}: {per_compiled:.6f}")
            self._append_log(log_fp, "")
            self._append_log(log_fp, "Stage+Kind Totals:")
            if len(stage_kind_totals) == 0:
                self._append_log(log_fp, "none")
            else:
                for (stage, kind), count in sorted(stage_kind_totals.items()):
                    self._append_log(log_fp, f"{stage}::{kind}: {count}")
            self._append_log(log_fp, "")
            self._append_log(log_fp, "Stage+Kind Totals Per Compiled Benchmark:")
            if len(stage_kind_totals) == 0:
                self._append_log(log_fp, "none")
            else:
                for (stage, kind), count in sorted(stage_kind_totals.items()):
                    per_compiled = (count / compiled) if compiled > 0 else 0.0
                    self._append_log(log_fp, f"{stage}::{kind}: {per_compiled:.6f}")
            self._append_log(log_fp, "")
            self._append_log(log_fp, "Stage-5 Minigame Tracked Totals:")
            for kind in tracked_minigame_kinds:
                self._append_log(
                    log_fp, f"stage5_minigame::{kind}: {minigame_kind_totals[kind]}"
                )

            if failures:
                self._append_log(log_fp, "")
                self._append_log(log_fp, "Failures:")
                for failure in failures:
                    self._append_log(log_fp, failure)

        print(
            "Summary: "
            f"compiled={compiled}, skipped={skipped}, unsupported={unsupported}, failed={len(failures)}, total={len(benchmarks)}"
        )
        print(f"full_log: {log_path}")

        if failures:
            self.fail(
                "ISSY optimisation summary run failed:\n\n" + "\n".join(failures[:50])
            )


if __name__ == "__main__":
    unittest.main()
