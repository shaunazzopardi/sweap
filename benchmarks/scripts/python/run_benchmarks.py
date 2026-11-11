#!/usr/bin/env python3
"""Run synthesis benchmarks in Sweap, TSL, RPG, or Issy format.

Examples:
  python run_benchmarks.py sweap --input benchmarks/sweap/finite --dual --backend strix
  python run_benchmarks.py issy --output my-results.csv --no-verify
  python run_benchmarks.py --resume my-results.csv

Use --resume to append to an existing CSV. A new --output never overwrites an
existing file. Settings in CSV.json are restored on resume; explicit conflicting
settings are rejected. Legacy CSVs without metadata use the requested settings.
The file column uses paths relative to --input, so equal basenames remain distinct.
All recorded results (including timeouts/errors) are skipped on resume.

Defaults: semml, one worker, parsing 10s, synthesis 20s for Sweap / 50s otherwise,
verification enabled with a 10s limit, and 50 GiB per timed process. Use -1 for
an unlimited phase timeout.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import csv
from datetime import datetime, timezone
import fnmatch
import gc
import json
import logging
import math
import multiprocessing
import os
from pathlib import Path
import sys
import time

import psutil

REPO = Path(__file__).resolve().parents[3]
FORMATS = {
    "sweap": ("sweap", {".prog"}),
    "tsl": ("raboniel", {".tsl", ".tslmt", ".tslt"}),
    "rpg": ("rpgsolve", {".rpg"}),
    "issy": ("issy", {".issy"}),
}
FIELDS = [
    "file",
    "realisable",
    "verification",
    "parse_time_seconds",
    "synthesis_time_seconds",
    "total_time_seconds",
]
DEFAULTS = {
    "backend": "semml",
    "dual": False,
    "dual_fallback": False,
    "workers": 1,
    "parse_timeout": 10.0,
    "synthesis_timeout": 50.0,
    "verification_timeout": 10.0,
    "memory_gb": 50.0,
    "synthesis_memory_limit_mb": None,
    "bound": -1,
    "verify": True,
    "debug": False,
    "finite": False,
    "lazy": False,
    "only_safety": False,
    "no_binary_enc": False,
    "abstraction_backend": "effects",
    "incremental_smt": True,
    "state_scopes": True,
    "chain_scopes": True,
    "location_constant_simplify": False,
}


def kill_solver_processes() -> None:
    """Clean up this runner's solvers without killing concurrent batches."""
    for process in psutil.Process().children(recursive=True):
        try:
            if process.name() in {"strix", "semml"}:
                process.kill()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue


def parser() -> argparse.ArgumentParser:
    cli = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    cli.add_argument("format", nargs="?", choices=FORMATS)
    cli.add_argument(
        "--input",
        type=Path,
        help="Input file or directory; defaults to the format's benchmark directory",
    )

    output = cli.add_mutually_exclusive_group()
    output.add_argument("--output", type=Path, help="Create a new CSV at this path")
    output.add_argument(
        "--resume", type=Path, help="Append missing cases to an existing CSV"
    )
    cli.add_argument(
        "--output-dir", type=Path, help="Directory for automatically named CSVs"
    )

    cli.add_argument("--backend", choices=("strix", "semml"))
    cli.add_argument("--abstraction-backend", choices=("effects",))
    cli.add_argument(
        "--workers", type=int, help="Worker processes per synthesis (default: 1)"
    )
    for name in (
        "parse-timeout",
        "synthesis-timeout",
        "verification-timeout",
        "memory-gb",
    ):
        cli.add_argument("--" + name, type=float)
    cli.add_argument("--synthesis-memory-limit-mb", type=int)
    cli.add_argument("--bound", type=int)

    for name in (
        "dual",
        "dual-fallback",
        "verify",
        "debug",
        "finite",
        "lazy",
        "only-safety",
        "incremental-smt",
        "state-scopes",
        "chain-scopes",
        "location-constant-simplify",
    ):
        cli.add_argument(
            "--" + name, action=argparse.BooleanOptionalAction, default=None
        )
    cli.add_argument(
        "--no-binary-enc", dest="no_binary_enc", action="store_true", default=None
    )
    cli.add_argument("--binary-enc", dest="no_binary_enc", action="store_false")

    cli.add_argument(
        "--include",
        action="append",
        default=[],
        help="Include relative paths matching this glob (repeatable)",
    )
    cli.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Exclude relative paths matching this glob (repeatable)",
    )
    cli.add_argument(
        "--limit", type=int, help="Maximum number of not-yet-completed cases"
    )
    cli.add_argument(
        "--list",
        action="store_true",
        help="List pending inputs without running or writing results",
    )

    return cli


def metadata_path(csv_path: Path) -> Path:
    return csv_path.with_suffix(csv_path.suffix + ".json")


def resolve_settings(args, default_format=None, defaults=None) -> dict:
    saved = None
    if args.resume:
        if not args.resume.is_file():
            raise ValueError(f"Resume CSV does not exist: {args.resume}")
        sidecar = metadata_path(args.resume)
        if sidecar.exists():
            saved = json.loads(sidecar.read_text())["settings"]

    kind = args.format or (saved or {}).get("format") or default_format
    if kind not in FORMATS:
        raise ValueError(
            "Specify sweap, tsl, rpg, or issy (or resume a CSV with saved settings)"
        )

    # Apply defaults, saved run settings, and explicit CLI overrides in that order.
    settings = dict(DEFAULTS)
    settings["synthesis_timeout"] = 20.0 if kind == "sweap" else 50.0
    settings.update(defaults or {})
    if saved:
        settings.update(saved)

    settings["format"] = kind
    settings["input"] = str(
        (
            args.input
            or Path(settings.get("input", REPO / "benchmarks" / FORMATS[kind][0]))
        ).resolve()
    )
    for key in DEFAULTS:
        value = getattr(args, key)
        if value is not None:
            settings[key] = value

    if saved:
        conflicts = [key for key in saved if settings[key] != saved[key]]
        if conflicts:
            raise ValueError(
                "Resume settings differ from the saved run: " + ", ".join(conflicts)
            )

    if settings["workers"] < 1:
        raise ValueError("--workers must be positive")

    for key in ("parse_timeout", "synthesis_timeout", "verification_timeout"):
        value = settings[key]
        if not math.isfinite(value) or (value <= 0 and value != -1):
            raise ValueError(
                f"--{key.replace('_', '-')} must be positive, or -1 for no timeout"
            )

    if not math.isfinite(settings["memory_gb"]) or settings["memory_gb"] <= 0:
        raise ValueError("--memory-gb must be positive")
    if (
        settings["synthesis_memory_limit_mb"] is not None
        and settings["synthesis_memory_limit_mb"] <= 0
    ):
        raise ValueError("--synthesis-memory-limit-mb must be positive")

    if settings["bound"] < -1:
        raise ValueError("--bound must be -1 or nonnegative")
    if settings["finite"] and (settings["lazy"] or settings["no_binary_enc"]):
        raise ValueError("--finite cannot be combined with --lazy or --no-binary-enc")
    if args.limit is not None and args.limit < 1:
        raise ValueError("--limit must be positive")

    return settings


def output_name(settings: dict) -> str:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    tags = [("d" if settings["dual"] else "") + settings["backend"]]

    for key, tag in (
        ("parse_timeout", "p"),
        ("synthesis_timeout", "s"),
        ("verification_timeout", "v"),
        ("memory_gb", "m"),
        ("workers", "w"),
    ):
        tags.append(tag + format(settings[key], "g").replace(".", "p"))

    tags.append("verify" if settings["verify"] else "noverify")
    for key, tag in (
        ("dual_fallback", "fallback"),
        ("debug", "debug"),
        ("finite", "finite"),
        ("lazy", "lazy"),
        ("only_safety", "safety"),
        ("no_binary_enc", "nobin"),
        ("location_constant_simplify", "locconst"),
    ):
        if settings[key]:
            tags.append(tag)

    for key, tag in (
        ("incremental_smt", "noinc"),
        ("state_scopes", "nostatescopes"),
        ("chain_scopes", "nochainscopes"),
    ):
        if not settings[key]:
            tags.append(tag)

    if settings["synthesis_memory_limit_mb"] is not None:
        tags.append(f"sm{settings['synthesis_memory_limit_mb']}")
    if settings["bound"] != -1:
        tags.append(f"b{settings['bound']}")

    return f"{stamp}-{settings['format']}-{'-'.join(tags)}.csv"


def discover(settings, includes=(), excludes=()) -> dict[str, Path]:
    root = Path(settings["input"])
    if not root.exists():
        raise ValueError(f"Input does not exist: {root}")

    extensions = FORMATS[settings["format"]][1]
    cases = {}
    if root.is_file():
        candidates = [root]
    else:
        candidates = []
        for directory, dirs, files in os.walk(root):
            dirs[:] = sorted(
                d for d in dirs
                if d not in {"logs", "results", ".git", "__pycache__"}
            )
            candidates.extend(Path(directory) / name for name in sorted(files))

    for source in candidates:
        if source.suffix.lower() not in extensions:
            continue
        key = source.name if root.is_file() else source.relative_to(root).as_posix()
        if includes and not any(
            fnmatch.fnmatchcase(key, pattern) for pattern in includes
        ):
            continue
        if any(fnmatch.fnmatchcase(key, pattern) for pattern in excludes):
            continue
        cases[key] = source

    return dict(sorted(cases.items()))


def read_results(path: Path, cases: dict, legacy: bool):
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        fields = reader.fieldnames or []
        if "file" not in fields or "realisable" not in fields:
            raise ValueError(f"Invalid results CSV header: {path}")
        rows = list(reader)

    processed = set()
    for row in rows:
        key = row["file"]
        if not key or row.get("realisable") in (None, "") or None in row:
            raise ValueError(f"Invalid or incomplete result row in {path}")
        if legacy and "/" not in key:
            matches = [candidate for candidate in cases if Path(candidate).name == key]
            if len(matches) > 1:
                raise ValueError(
                    f"Legacy CSV basename {key!r} is ambiguous; "
                    "use relative paths in its file column"
                )
            if matches:
                key = matches[0]
        processed.add(key)

    return fields, rows, processed


def initialize_results(path: Path, settings, resume: bool, fields=None, rows=None):
    if resume:
        fields = list(fields)
        # Keep existing columns and values, including legacy verification_10s.
        if not {"verification", "verification_10s"}.intersection(fields):
            fields.append("verification")
            temporary = path.with_suffix(path.suffix + ".tmp")
            with temporary.open("x", newline="") as stream:
                writer = csv.DictWriter(stream, fieldnames=fields)
                writer.writeheader()
                writer.writerows(rows)
            temporary.replace(path)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        fields = list(FIELDS)
        with path.open("x", newline="") as stream:
            csv.DictWriter(stream, fieldnames=fields).writeheader()

    sidecar = metadata_path(path)
    if not sidecar.exists():
        sidecar.write_text(
            json.dumps(
                {"settings": settings, "file_keys": "legacy" if resume else "relative"},
                indent=2,
            ) + "\n"
        )

    return fields


def parse_tsl(text, name):
    from parsing.string_to_ltl import string_to_ltlmt
    from parsing.string_to_ltlmt import ToProgram

    formulas, declarations = string_to_ltlmt(text)
    return ToProgram().ltlmt2prog(formulas, name, declarations)


def verify_controller(program, objective, hoa):
    import config
    from analysis.compatibility_checking.log_replay_verifier import (
        verify_wrapped_hoa_against_program,
    )

    conf = config.Config.getConfig()
    original_log, original_verify = conf.log, conf.verify_controller

    try:
        conf.log, conf.verify_controller = None, False
        verify_wrapped_hoa_against_program(program, objective, None, hoa)
        return True
    finally:
        conf.log, conf.verify_controller = original_log, original_verify


class Runtime:
    """Dependencies and process boundaries for the shared benchmark workflow."""

    def __init__(self):
        sys.path.insert(0, str(REPO))
        sys.path.insert(0, str(REPO / "src"))
        os.environ["PATH"] = os.pathsep.join(
            [
                str(Path(sys.executable).parent),
                str(REPO / "binaries"),
                os.environ.get("PATH", ""),
            ]
        )

        # Defer synthesis dependencies so --help and --list stay lightweight.
        import config
        from pysmt.environment import Environment

        from parsing.string_to_program import string_to_program
        from parsing.string_to_issy import string_to_issy
        from parsing.string_to_rpg import rpg_parsec
        from programs.util import reset_caches as program_reset
        from prop_lang.util import reset_caches as prop_reset
        from benchmarks.scripts.python.resource_limits import run_with_timeout_and_memory_limit
        from synthesis.synthesis import synthesize

        self.conf = config.Config.getConfig()
        self.environment = Environment
        self.parsers = {
            "sweap": string_to_program,
            "issy": string_to_issy,
            "rpg": rpg_parsec,
            "tsl": parse_tsl,
        }
        self.resetters = (program_reset, prop_reset)
        self.run_limited = run_with_timeout_and_memory_limit
        self.synthesize = synthesize

    def reset(self):
        gc.collect()
        for reset in self.resetters:
            reset()

    @contextmanager
    def configured(self, settings, source, log, dual):
        values = {
            "backend": settings["backend"],
            "dual": dual,
            "workers": settings["workers"],
            "debug": settings["debug"],
            "finite_synthesis": settings["finite"],
            "only_safety": settings["only_safety"],
            "no_binary_enc": settings["no_binary_enc"],
            "eager_fairness": not (
                settings["lazy"] or settings["only_safety"] or settings["no_binary_enc"]
            ),
            "abstraction_backend": settings["abstraction_backend"],
            "verify_controller": False,
            "synthesis_memory_limit_mb": settings["synthesis_memory_limit_mb"],
            "opt_incremental_smt": settings["incremental_smt"],
            "opt_state_scopes": settings["state_scopes"],
            "opt_chain_scopes": settings["chain_scopes"],
            "opt_location_constant_simplify": settings["location_constant_simplify"],
            "name": source.name,
            "log": str(log / "synthesis"),
        }
        saved = {key: getattr(self.conf, key) for key in values}

        try:
            for key, value in values.items():
                setattr(self.conf, key, value)

            replay = dict.fromkeys(("program", "issy", "tsl", "rpg"))
            replay[
                "program" if settings["format"] == "sweap" else settings["format"]
            ] = str(source)
            replay.update(
                translate=None,
                synthesise=settings["bound"],
                finite_synthesise=settings["finite"],
                model_check=None,
                out_dot=None,
                debug=settings["debug"],
                log=self.conf.log,
                tlsf=None,
                synthesis_backend=self.conf.backend,
                abstraction_backend=self.conf.abstraction_backend,
                verify_controller=False,
                workers=self.conf.workers,
                synthesis_memory_limit_mb=self.conf.synthesis_memory_limit_mb,
                lazy=settings["lazy"],
                only_safety=self.conf.only_safety,
                no_binary_enc=self.conf.no_binary_enc,
                dual=dual,
            )
            logging.info("Input args: %s", replay)
            logging.info("Benchmark settings: %s", settings)

            yield
        finally:
            for key, value in saved.items():
                setattr(self.conf, key, value)

    def parse(self, source, settings):
        text = source.read_text()
        args = [text] if settings["format"] == "sweap" else [text, source.stem]

        return self.run_limited(
            self.parsers[settings["format"]],
            args,
            settings["parse_timeout"],
            settings["memory_gb"],
        )

    def solve(self, program, objective, settings):
        try:
            return self.run_limited(
                self.synthesize,
                [program, objective, None, settings["bound"]],
                settings["synthesis_timeout"],
                settings["memory_gb"],
            )
        finally:
            kill_solver_processes()

    def verify(self, program, objective, hoa, settings):
        return self.run_limited(
            verify_controller,
            [program, objective, hoa],
            settings["verification_timeout"],
            settings["memory_gb"],
        )


def failure(value, phase=""):
    suffix = f"({phase})" if phase else ""
    if value == "Timeout":
        return "TO" + suffix
    if value == "Memory limit exceeded" or "java.lang.OutOfMemoryError" in str(value):
        return "OOM" + suffix
    return f"ERR{suffix}: {value}"


def run_case(source, key, settings, log, runtime):
    result = dict(
        file=key,
        realisable="N/A",
        verification="N/A",
        parse_time_seconds=0.0,
        synthesis_time_seconds=0.0,
        total_time_seconds=0.0,
    )
    started = time.monotonic()
    modes = [settings["dual"]]
    if settings["dual_fallback"]:
        modes.append(not settings["dual"])

    try:
        with runtime.environment():
            for attempt, dual in enumerate(modes):
                with runtime.configured(settings, source, log, dual):
                    before = time.monotonic()
                    success, parsed = runtime.parse(source, settings)
                    result["parse_time_seconds"] += time.monotonic() - before
                    if not success:
                        result["realisable"] = failure(
                            parsed, "parse-dual-alt" if attempt else "parse"
                        )
                        break

                    program, objective = parsed
                    before = time.monotonic()
                    success, hoa = runtime.solve(program, objective, settings)
                    result["synthesis_time_seconds"] += time.monotonic() - before
                    if not success:
                        result["realisable"] = failure(hoa)
                        continue

                    verdict = hoa.realisable if hoa is not None else "N/A"
                    result["realisable"] = (
                        f"{verdict} (dual-alt)" if attempt else verdict
                    )

                    if hoa is not None and settings["verify"]:
                        try:
                            verified, value = runtime.verify(
                                program, objective, hoa, settings
                            )
                            if verified:
                                result["verification"] = True
                            elif (
                                "does not enforce the required LTL property"
                                in str(value)
                            ):
                                result["verification"] = False
                            else:
                                result["verification"] = failure(value, "verif")
                        except Exception as error:
                            logging.exception("Verification failed: %s", source)
                            result["verification"] = failure(error, "verif")
                    break

    except Exception as error:
        logging.exception("Benchmark failed: %s", source)
        result["realisable"] = f"ERR: {error}"

    result["total_time_seconds"] = time.monotonic() - started
    for field in ("parse_time_seconds", "synthesis_time_seconds", "total_time_seconds"):
        result[field] = round(result[field], 3)

    return result


def main(argv=None, *, default_format=None, defaults=None):
    cli = parser()
    args = cli.parse_args(argv)
    csv.field_size_limit(sys.maxsize)

    try:
        settings = resolve_settings(args, default_format, defaults)
        all_cases = discover(settings)
        cases = discover(settings, args.include, args.exclude)
        if not cases:
            raise ValueError("No matching benchmarks found")

        fields, rows, processed = None, None, set()
        if args.resume:
            fields, rows, processed = read_results(
                args.resume,
                all_cases,
                legacy=(
                    not metadata_path(args.resume).exists()
                    or json.loads(metadata_path(args.resume).read_text()).get(
                        "file_keys"
                    ) == "legacy"
                ),
            )

        pending = [
            (key, source) for key, source in cases.items() if key not in processed
        ]
        if args.limit:
            pending = pending[:args.limit]

        if args.list:
            for key, _ in pending:
                print(key)
            print(
                f"{len(pending)} pending; "
                f"{sum(k in processed for k in cases)} already recorded"
            )
            return 0

        root = Path(settings["input"])
        output_dir = args.output_dir or (
            (root.parent if root.is_file() else root) / "results"
        )
        output = (
            args.resume or args.output or output_dir / output_name(settings)
        ).resolve()
        if not args.resume and (output.exists() or metadata_path(output).exists()):
            raise ValueError(f"Output already exists; use --resume to append: {output}")

        fields = initialize_results(output, settings, bool(args.resume), fields, rows)

    except (ValueError, OSError, KeyError) as error:
        cli.error(str(error))

    print(
        f"{settings['format']}: {len(pending)} pending; results: {output}",
        flush=True,
    )
    if not pending:
        return 0

    if "fork" in multiprocessing.get_all_start_methods():
        multiprocessing.set_start_method("fork", force=True)
    runtime = Runtime()

    for index, (key, source) in enumerate(pending, 1):
        runtime.reset()

        log = (
            output.parent
            / output.stem
            / "logs"
            / key
            / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        )
        log.mkdir(parents=True)
        logging.basicConfig(
            filename=log / "run.log",
            encoding="utf-8",
            level=logging.INFO,
            format="%(asctime)s %(levelname)s %(message)s",
            force=True,
        )

        print(f"[{index}/{len(pending)}] {key}", flush=True)
        result = run_case(source, key, settings, log, runtime)

        row = {field: result.get(field, "") for field in fields}
        if "verification_10s" in fields:
            row["verification_10s"] = result["verification"]
        with output.open("a", newline="") as stream:
            csv.DictWriter(stream, fieldnames=fields).writerow(row)

        print(
            f"  realisable={result['realisable']} "
            f"verification={result['verification']}",
            flush=True,
        )

    print(f"Finished: {output}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
