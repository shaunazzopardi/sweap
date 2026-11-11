#!/usr/bin/env python3
"""Check Sweap-to-Issy exports and compare original/round-trip Issy verdicts.

Run with the Sweap virtual environment's Python. Each translation gets a fresh
process; no pySMT symbols or parser configuration leak between benchmarks.

Examples:
  .venv/bin/python benchmarks/scripts/python/check_issy_translations.py --issy /path/to/issy
  .venv/bin/python benchmarks/scripts/python/check_issy_translations.py --list --formats sweap
  .venv/bin/python benchmarks/scripts/python/check_issy_translations.py --issy /path/to/issy \
      --root benchmarks/issy --solve-timeout 300

By default, scan benchmarks/ and tests/test-problems/, excluding logs/results.
TSL suffixes .tsl, .tslmt, and .tslt all use Sweap's --tsl input path; unsupported
dialects are reported as translation failures. Verdict comparisons run only for
original Issy inputs. --skip-verdicts disables solving. --acceptance compile
selects syntax-only checks; the default also invokes --to-game.

Each case retains translated.issy, stdout/stderr logs, and result.json. Aggregate
results.csv/results.json and manifest.json are written to --output (default: a
new timestamped directory under benchmarks/results/issy-translations). Results
are saved after every file. Exit status is 1 on failures or inconclusive verdict
comparisons, 0 when all selected checks pass, and 2 for invalid invocation.
"""

from __future__ import annotations

import argparse
import csv
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[3]
EXTENSIONS = {
    ".prog": "sweap", ".issy": "issy", ".rpg": "rpg",
    ".tsl": "tsl", ".tslmt": "tsl", ".tslt": "tsl",
}
INPUT_FLAGS = {"sweap": "--p", "issy": "--issy", "rpg": "--rpg", "tsl": "--tsl"}
EXCLUDED_DIRS = {".git", ".venv", "__pycache__", "logs", "results", "output"}
FIELDS = [
    "file", "format", "translation", "compile", "to_game", "acceptance",
    "original_solve", "original_verdict", "translated_solve",
    "translated_verdict", "comparison", "artifacts",
]


def display_path(path: Path) -> str:
    try:
        return path.relative_to(REPO).as_posix()
    except ValueError:
        return str(path)


def discover(roots: list[Path], formats: set[str], patterns: list[str]) -> list[Path]:
    found = set()
    for root in roots:
        if not root.exists():
            raise ValueError(f"Input root does not exist: {root}")
        if root.is_file():
            candidates = [root]
            if root.suffix.lower() not in EXTENSIONS:
                raise ValueError(f"Unsupported input extension: {root}")
        else:
            candidates = []
            for directory, dirs, files in os.walk(root):
                dirs[:] = sorted(d for d in dirs if d not in EXCLUDED_DIRS)
                candidates.extend(Path(directory) / name for name in sorted(files))
        for candidate in candidates:
            path = candidate.resolve()
            if EXTENSIONS.get(path.suffix.lower()) not in formats:
                continue
            if patterns and not any(
                fnmatch.fnmatchcase(display_path(path), pattern) for pattern in patterns
            ):
                continue
            found.add(path)
    return sorted(found, key=display_path)


def run_stage(command: list[str], directory: Path, stage: str, timeout: float) -> dict:
    stdout_path = directory / f"{stage}.stdout.log"
    stderr_path = directory / f"{stage}.stderr.log"
    started = time.monotonic()
    result = {
        "command": command, "status": "error", "returncode": None,
        "stdout": str(stdout_path), "stderr": str(stderr_path),
    }
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        try:
            process = subprocess.Popen(
                command, cwd=directory, stdout=stdout, stderr=stderr,
                start_new_session=(os.name == "posix"),
            )
        except OSError as error:
            result["error"] = str(error)
        else:
            try:
                result["returncode"] = process.wait(timeout=timeout)
                result["status"] = "pass" if process.returncode == 0 else "error"
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                # Kill the whole group, including parser workers and solver children.
                if os.name == "posix":
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                else:
                    process.kill()
                process.wait()
                if isinstance(error, KeyboardInterrupt):
                    raise
                result["status"] = "timeout"
    result["seconds"] = round(time.monotonic() - started, 3)
    return result


def verdict(result: dict) -> str | None:
    """Accept only an unambiguous standalone verdict from a successful solve."""
    if result["status"] != "pass":
        return None
    lines = Path(result["stdout"]).read_text(errors="replace").splitlines()
    answers = {
        line.strip().lower() for line in lines
        if line.strip().lower() in {"realizable", "unrealizable"}
    }
    return answers.pop() if len(answers) == 1 else None


def translate_worker(source: Path, destination: Path, workers: int) -> None:
    # Import Sweap only in this isolated worker, using the normal CLI input paths.
    import multiprocessing

    if os.name == "posix":
        multiprocessing.set_start_method("fork", force=True)
    sys.path.insert(0, str(REPO / "src"))
    from main import process_args, setup_argument_parser

    arguments = setup_argument_parser().parse_args([
        INPUT_FLAGS[EXTENSIONS[source.suffix.lower()]], str(source),
        "--translate", "issy", "--workers", str(workers),
    ])
    program, objective = process_args(arguments)
    destination.write_text(program.to_issy(objective))


def check_case(source: Path, directory: Path, args, issy_command: list[str]) -> dict:
    directory.mkdir()
    translated = directory / "translated.issy"
    row = {field: "not_run" for field in FIELDS}
    row.update(
        file=display_path(source), format=EXTENSIONS[source.suffix.lower()],
        artifacts=str(directory), original_verdict="", translated_verdict="",
        comparison="not_applicable",
    )
    stages = {}
    command = [
        sys.executable, str(Path(__file__).resolve()), "--_translate",
        str(source), str(translated), str(args.workers),
    ]
    stages["translation"] = run_stage(command, directory, "translation", args.translation_timeout)
    row["translation"] = stages["translation"]["status"]
    if row["translation"] == "pass" and not translated.is_file():
        row["translation"] = stages["translation"]["status"] = "error"
        stages["translation"]["error"] = "Translation produced no file"
    if row["translation"] == "pass":
        stages["compile"] = run_stage(
            issy_command + ["--compile", str(translated)],
            directory, "compile", args.acceptance_timeout,
        )
        row["compile"] = stages["compile"]["status"]
        row["acceptance"] = row["compile"]
        if row["compile"] == "pass" and args.acceptance == "to-game":
            stages["to_game"] = run_stage(
                issy_command + ["--to-game", str(translated)],
                directory, "to_game", args.acceptance_timeout,
            )
            row["to_game"] = stages["to_game"]["status"]
            row["acceptance"] = row["to_game"]
    else:
        row["acceptance"] = "not_run"
    if row["format"] == "issy":
        row["comparison"] = "skipped" if args.skip_verdicts else "inconclusive"
        if not args.skip_verdicts:
            # Run the original even when translation fails, to distinguish failures.
            for label, path in (("original", source), ("translated", translated)):
                if label == "translated" and row["acceptance"] != "pass":
                    continue
                key = f"{label}_solve"
                stages[key] = run_stage(
                    issy_command + ["--solve", str(path)],
                    directory, key, args.solve_timeout,
                )
                row[key] = stages[key]["status"]
                answer = verdict(stages[key])
                if answer is None and row[key] == "pass":
                    row[key] = stages[key]["status"] = "no_verdict"
                row[f"{label}_verdict"] = answer or ""
            if row["original_verdict"] and row["translated_verdict"]:
                row["comparison"] = (
                    "match" if row["original_verdict"] == row["translated_verdict"]
                    else "mismatch"
                )
    record = {"summary": row, "stages": stages}
    (directory / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    result.add_argument("--issy", default="issy", help="Issy v3 executable (not a stdin-only wrapper)")
    result.add_argument("--issy-args", default="", help="Extra Issy arguments, shell-quoted as one string")
    result.add_argument("--root", type=Path, action="append", help="Input directory or file; repeatable")
    result.add_argument("--formats", nargs="+", choices=sorted(INPUT_FLAGS), default=sorted(INPUT_FLAGS))
    result.add_argument("--include", action="append", default=[], help="Glob on repository-relative path; repeatable")
    result.add_argument("--limit", type=int, help="Check only the first N selected files")
    result.add_argument("--output", type=Path, help="New directory for translations, logs, and summaries")
    result.add_argument("--jobs", type=int, default=1, help="Benchmarks checked concurrently")
    result.add_argument("--workers", type=int, default=1, help="Sweap parser workers per translation")
    result.add_argument("--translation-timeout", type=float, default=60)
    result.add_argument("--acceptance-timeout", type=float, default=60)
    result.add_argument("--solve-timeout", type=float, default=120, help="Seconds per Issy solve, for each version")
    result.add_argument("--acceptance", choices=("compile", "to-game"), default="to-game")
    result.add_argument("--skip-verdicts", action="store_true", help="Only check acceptance, even for Issy inputs")
    result.add_argument("--list", action="store_true", help="List selected benchmarks without running anything")
    return result


def main() -> int:
    # Private subprocess entry point keeps parent discovery/reporting dependency-free.
    if len(sys.argv) == 5 and sys.argv[1] == "--_translate":
        translate_worker(Path(sys.argv[2]), Path(sys.argv[3]), int(sys.argv[4]))
        return 0
    cli = parser()
    args = cli.parse_args()
    if args.jobs < 1 or args.workers < 1 or (args.limit is not None and args.limit < 1):
        cli.error("--jobs, --workers and --limit must be positive")
    if min(args.translation_timeout, args.acceptance_timeout, args.solve_timeout) <= 0:
        cli.error("timeouts must be positive")
    roots = [p.resolve() for p in (args.root or [REPO / "benchmarks", REPO / "tests/test-problems"])]
    try:
        sources = discover(roots, set(args.formats), args.include)
    except ValueError as error:
        cli.error(str(error))
    if args.limit:
        sources = sources[:args.limit]
    if not sources:
        cli.error("No benchmarks selected")
    if args.list:
        for source in sources:
            print(f"{EXTENSIONS[source.suffix.lower()]}\t{display_path(source)}")
        print(f"Selected {len(sources)} files", file=sys.stderr)
        return 0
    executable = shutil.which(args.issy)
    if executable is None:
        cli.error(f"Cannot find Issy executable: {args.issy}")
    issy_command = [str(Path(executable).resolve())] + shlex.split(args.issy_args)
    output = (args.output or REPO / "benchmarks/results/issy-translations" /
              datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    if output.exists() and any(output.iterdir()):
        cli.error(f"Output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    os.environ["PATH"] = os.pathsep.join([
        str(Path(sys.executable).parent), str(REPO / "binaries"), os.environ.get("PATH", ""),
    ])
    manifest = {
        "python": sys.executable, "issy_command": issy_command,
        "options": vars(args), "sources": [str(source) for source in sources],
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    records = []
    print(f"Checking {len(sources)} files; artifacts: {output}", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool, (output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        stream.flush()
        pending = []
        for index, source in enumerate(sources, 1):
            key = hashlib.sha256(str(source).encode()).hexdigest()[:12]
            directory = output / f"{index:04d}-{key}"
            pending.append(pool.submit(check_case, source, directory, args, issy_command))
        for index, future in enumerate(as_completed(pending), 1):
            record = future.result()
            records.append(record)
            row = record["summary"]
            writer.writerow(row)
            stream.flush()
            (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
            print(
                f"[{index}/{len(sources)}] {row['file']}: translation={row['translation']} "
                f"acceptance={row['acceptance']} comparison={row['comparison']}", flush=True,
            )
    failures = sum(
        r["summary"]["acceptance"] != "pass"
        or r["summary"]["comparison"] in {"mismatch", "inconclusive"}
        for r in records
    )
    print(f"Finished: {len(records)} checked; {failures} failed or inconclusive. Results: {output / 'results.csv'}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
