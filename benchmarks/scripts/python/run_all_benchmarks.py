#!/usr/bin/env python3
"""Run all benchmark formats with default settings, then with --dual.

Usage: .venv3.12/bin/python benchmarks/scripts/python/run_all_benchmarks.py
Optional: --output-dir /path/to/results
Resume the latest batch: --resume
Resume a specific batch: --resume /path/to/results
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys


REPO = Path(__file__).resolve().parents[3]
RUNNER = Path(__file__).with_name("run_benchmarks.py")
RESULTS = REPO / "benchmarks/results"
FORMATS = ("sweap", "tsl", "issy", "rpg")


def latest_batch():
    directories = sorted(
        path for path in RESULTS.glob("*")
        if path.is_dir() and re.fullmatch(r"\d{8}T\d{12}Z", path.name)
    )
    if not directories:
        raise ValueError(f"No previous benchmark batch found in {RESULTS}")
    return directories[-1]


def resume_files(directory):
    """Use saved settings to identify each format/configuration's CSV."""
    existing = {}
    for csv in sorted(directory.glob("*.csv")):
        sidecar = csv.with_suffix(csv.suffix + ".json")
        settings = json.loads(sidecar.read_text())["settings"]
        kind, dual = settings["format"], settings["dual"]
        if kind not in FORMATS or not isinstance(dual, bool):
            raise ValueError(f"Invalid benchmark settings in {sidecar}")
        key = (kind, dual)
        if key in existing:
            raise ValueError(f"Multiple CSVs for {kind}, dual={dual} in {directory}")
        existing[key] = csv
    return existing


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--output-dir", type=Path)
    output.add_argument(
        "--resume", nargs="?", const=True, type=Path, metavar="DIRECTORY",
        help="Resume a batch directory (default: latest timestamped batch)",
    )
    args = parser.parse_args()

    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    try:
        if args.resume is not None:
            output_dir = (latest_batch() if args.resume is True else args.resume).resolve()
            if not output_dir.is_dir():
                raise ValueError(f"Benchmark batch directory does not exist: {output_dir}")
            existing = resume_files(output_dir)
        else:
            output_dir = (args.output_dir or RESULTS / timestamp).resolve()
            existing = {}
    except (OSError, ValueError, KeyError) as error:
        parser.error(str(error))
    env = os.environ.copy()
    env["PATH"] = str(REPO / "binaries") + os.pathsep + env.get("PATH", "")
    env["PYTHONPATH"] = str(REPO / "src") + os.pathsep + env.get("PYTHONPATH", "")
    failures = []

    print(f"Results directory: {output_dir}", flush=True)
    # Solver cleanup in the runner is global, so these calls must be sequential.
    for dual in (False, True):
        for kind in FORMATS:
            label = f"{kind}: {'dual' if dual else 'default'}"
            command = [sys.executable, str(RUNNER), kind]
            previous = existing.get((kind, dual))
            if previous is not None:
                command += ["--resume", str(previous)]
            else:
                command += ["--output-dir", str(output_dir)]
            if dual:
                command.append("--dual")

            print(f"\nRunning {label}", flush=True)
            result = subprocess.run(command, cwd=REPO, env=env, check=False)
            if result.returncode:
                failures.append(label)

    if failures:
        print("Failed runs: " + ", ".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
