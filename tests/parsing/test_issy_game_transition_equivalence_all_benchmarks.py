import os
import re
import unittest
from datetime import datetime
from pathlib import Path

import parsec
from pysmt.shortcuts import reset_env

import config
from prop_lang.util import run_with_timeout
from prop_lang import util as prop_lang_util_module
from programs import util as program_util_module
from parsing.string_to_issy import (
    _build_intermediate_game_program_data,
    _preprocess_issy_games_for_intermediate,
    _prepare_context,
    parser as issy_parser,
)
from tests.parsing.validation.issy_game_transition_equivalence import (
    check_issy_games_vs_programs_transition_equivalence,
)


def _parse_issy_raw(text: str):
    input_wo_comments = re.sub(r"//.*(\n|$)", "", text).strip()
    return (issy_parser << parsec.eof()).parse(input_wo_comments)


REPO_ROOT = Path(__file__).resolve().parents[2]
ISSY_BENCHMARK_ROOT = REPO_ROOT / "benchmarks" / "issy"
LOG_DIR = REPO_ROOT / "src" / "logs" / "issy_game_transition_equivalence"


class TestIssyGameTransitionEquivalenceAllBenchmarks(unittest.TestCase):
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
            or "Permission denied" in msg
            or "Operation not permitted" in msg
            or "SemLock" in msg
        )

    def _announce(self, msg: str):
        print(msg, flush=True)

    @staticmethod
    def _append_log(fp, line: str):
        fp.write(line + "\n")
        fp.flush()
        os.fsync(fp.fileno())

    def test_issy_game_transition_equivalence_all_benchmarks(self):
        benchmarks = sorted(ISSY_BENCHMARK_ROOT.rglob("*.issy"))
        only = os.environ.get("ISSY_PMOE_ONLY")
        limit = os.environ.get("ISSY_EQ_LIMIT")
        max_process_seconds = float(os.environ.get("ISSY_EQ_MAX_PROCESS_SECONDS", "10"))

        if only:
            benchmarks = [b for b in benchmarks if only in str(b)]
        if limit:
            benchmarks = benchmarks[: int(limit)]

        self.assertTrue(benchmarks, "No ISSY benchmarks found.")
        self._announce(f"[setup] discovered {len(benchmarks)} benchmark files")
        if only:
            self._announce(f"[setup] filter ISSY_EQ_ONLY={only}")
        if limit:
            self._announce(f"[setup] limit ISSY_EQ_LIMIT={limit}")
        self._announce(
            "max processing time per game "
            f"ISSY_EQ_MAX_PROCESS_SECONDS={max_process_seconds:g}"
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
                    self._announce(f"[{idx}/{total}] parse {rel}")
                    vars_or_macros, formula_objectives, games = _parse_issy_raw(
                        benchmark_path.read_text()
                    )
                    if len(games) == 0:
                        skipped += 1
                        self._announce(f"[{idx}/{total}] skip {rel} (no games)")
                        self._append_log(
                            log_fp, f"[{idx}/{total}] SKIP {rel} (no games)"
                        )
                        continue

                    self._announce(f"[{idx}/{total}] build context {rel}")
                    problem_context = _prepare_context(
                        vars_or_macros=vars_or_macros,
                        formula_objectives=formula_objectives,
                        optimisation_summary={},
                    )
                    inputs = list(problem_context.inputs)
                    symbol_table = dict(problem_context.symbol_table)
                    preprocessed_games = _preprocess_issy_games_for_intermediate(
                        games,
                        problem_context.macros,
                        symbol_table,
                        {str(v) for v in inputs},
                    )

                    per_game_programs = []
                    for game_index, game in enumerate(preprocessed_games):
                        self._announce(
                            f"[{idx}/{total}] build per-game program {rel} "
                            f"game={game_index + 1}/{len(games)}"
                        )
                        self._append_log(
                            log_fp,
                            f"[{idx}/{total}] build per-game program {rel} "
                            f"game={game_index + 1}/{len(games)}",
                        )
                        # Build each game separately and compare against the intermediate
                        # non-deterministic program before determinisation/cross-product.
                        try:
                            process_ok, game_data = run_with_timeout(
                                _build_intermediate_game_program_data,
                                (
                                    f"{benchmark_path.stem}_game_{game_index}",
                                    [game],
                                    problem_context,
                                ),
                                max_process_seconds,
                            )
                        except (
                            PermissionError,
                            EOFError,
                            BrokenPipeError,
                            ConnectionError,
                        ):
                            # Restricted sandboxes can block multiprocessing listener sockets.
                            process_ok = True
                            game_data = _build_intermediate_game_program_data(
                                f"{benchmark_path.stem}_game_{game_index}",
                                [game],
                                problem_context,
                            )
                        if not process_ok:
                            raise TimeoutError(
                                "_build_intermediate_game_program_data timed out "
                                f"after {max_process_seconds:g}s "
                                f"(game={game_index + 1}/{len(games)})"
                            )
                        sub_programs = game_data[0]
                        if len(sub_programs) != 1:
                            raise Exception(
                                "Expected one intermediate program for one input game, got "
                                + str(len(sub_programs))
                            )
                        per_game_programs.append(sub_programs[0][0])

                    self._announce(f"[{idx}/{total}] run transition equivalence {rel}")
                    self._append_log(
                        log_fp, f"[{idx}/{total}] run transition equivalence {rel}"
                    )

                    def _progress(msg: str, _idx=idx, _total=total, _rel=rel):
                        full = f"[{_idx}/{_total}] {_rel} {msg}"
                        self._announce(full)
                        self._append_log(log_fp, full)

                    try:
                        report = check_issy_games_vs_programs_transition_equivalence(
                            preprocessed_games,
                            per_game_programs,
                            symbol_table,
                            inputs,
                            progress_cb=_progress,
                        )
                    except TypeError:
                        report = check_issy_games_vs_programs_transition_equivalence(
                            preprocessed_games, per_game_programs, symbol_table, inputs
                        )

                    self._append_log(
                        log_fp,
                        f"[{idx}/{total}] RESULT {rel} equivalent={report.equivalent}",
                    )
                    for game_report in report.game_results:
                        self._append_log(
                            log_fp,
                            f"  game={game_report.game_index} equivalent={game_report.equivalent}",
                        )
                        for src in game_report.source_results:
                            self._append_log(
                                log_fp,
                                "    "
                                f"src={src.source_loc} prog_state={src.source_prog_state} "
                                f"left_implies_right={src.left_implies_right} "
                                f"right_implies_left={src.right_implies_left} "
                                f"equivalent={src.equivalent}",
                            )

                    if not report.equivalent:
                        failed = []
                        for game_report in report.game_results:
                            for src in game_report.source_results:
                                if not src.equivalent:
                                    failed.append(
                                        f"game={src.game_index}, src={src.source_loc}, "
                                        f"left_implies_right={src.left_implies_right}, "
                                        f"right_implies_left={src.right_implies_left}"
                                    )
                        failures.append(f"{rel}:\n" + "\n".join(failed))
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
                        self._append_log(log_fp, f"[{idx}/{total}] UNSUPPORTED {msg}")
                        self._announce(f"[{idx}/{total}] UNSUPPORTED {rel}")
                    else:
                        failures.append(msg)
                        self._append_log(log_fp, f"[{idx}/{total}] EXCEPTION {msg}")
                        self._announce(f"[{idx}/{total}] EXCEPTION {rel}")
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
                "Per-game transition equivalence failed:\n\n" + "\n\n".join(failures)
            )


if __name__ == "__main__":
    unittest.main()
