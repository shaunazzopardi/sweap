# Benchmarks

This directory contains benchmark inputs and scripts for running Sweap and
processing evaluation results. Commands below run from the repository root,
using the Python environment and solvers described in the
[installation instructions](../README.md#setup).

## Input collections

| Directory | Contents | Runner format |
| --- | --- | --- |
| `sweap/` | Sweap programs (`.prog`), including finite, full-LTL, and nondeterministic examples | `sweap` |
| `issy/` | Issy specifications (`.issy`) | `issy` |
| `rpgsolve/` | Reactive program games (`.rpg`) | `rpg` |
| `raboniel/` | TSL modulo theories specifications (`.tslmt`) | `tsl` |
| `popl25/` | Additional TSL modulo theories specifications (`.tslmt`) | `tsl` |
| `temos/` | TSL specifications (`.tslt` and `.tslmt`) | `tsl` |
| `tslmt2rpg/` | TSL modulo theories inputs for comparison with the TSL-to-RPG tool | `tsl` |

The default input directories are `sweap/`, `issy/`, `rpgsolve/`, and
`raboniel/` for their respective formats. Use `--input` to select another
collection, subdirectory, or individual file. Accepting a file extension does
not guarantee support for every dialect or theory used by that collection.

## Running benchmarks

Install the development requirements, which include the benchmark runner's
process-monitoring dependency, and expose the bundled tools and Python modules:

```bash
python -m pip install -r requirements-dev.txt
export PATH="$PWD/binaries:$PATH"
export PYTHONPATH="$PWD/src"
```

Preview a selection without running synthesis or writing results:

```bash
python benchmarks/scripts/python/run_benchmarks.py sweap \
    --input benchmarks/sweap/finite --list
```

Run one program or a collection:

```bash
python benchmarks/scripts/python/run_benchmarks.py sweap \
    --input benchmarks/sweap/finite/bloem-elevator-simple-5.prog \
    --output benchmarks/results/elevator.csv

python benchmarks/scripts/python/run_benchmarks.py issy --backend semml --dual

python benchmarks/scripts/python/run_benchmarks.py tsl \
    --input benchmarks/popl25
```

The default backend is SemML. By default, parsing has a 10-second limit,
synthesis has a 20-second limit for Sweap inputs and 50 seconds for the other
formats, and verification has a 10-second limit. Each timed process has a
50-GiB memory limit; synthesis uses one worker. Override these with
`--parse-timeout`, `--synthesis-timeout`, `--verification-timeout`,
`--memory-gb`, and `--workers`. Use `--no-verify` to disable verification.
Repeatable `--include` and `--exclude` glob filters and `--limit` narrow the
selection. Consult `--help` for all options and available backends.

Resume a CSV using its saved configuration:

```bash
python benchmarks/scripts/python/run_benchmarks.py \
    --resume benchmarks/results/elevator.csv
```

Resume skips every case already recorded, including errors and timeouts.
Use a new output CSV to retry those cases. New runs refuse to overwrite an
existing CSV or its settings file.

To run all four default collections, first in base mode and then in dual mode:

```bash
python benchmarks/scripts/python/run_all_benchmarks.py
python benchmarks/scripts/python/run_all_benchmarks.py --resume
```

The batch runner creates a timestamped directory under `benchmarks/results/`.
Use `--output-dir` to choose another destination, or `--resume DIRECTORY` to
resume a specific batch instead of the latest one.

## Results and logs

The single-format runner writes an automatically named CSV in a `results/`
subdirectory of the selected input directory (or beside the input file), unless
an output path or directory is supplied. Each CSV has a `.csv.json` settings
sidecar. Detailed per-case logs and synthesis
artifacts are stored beneath `<csv-stem>/logs/` beside the CSV.

CSV columns record the input path, synthesis verdict (`realisable`),
verification outcome, and parsing, synthesis, and total elapsed times in
seconds. Synthesis and verification outcomes are separate: a `True` synthesis
verdict does not imply successful verification. Inspect both columns for
errors, timeouts, or unavailable outcomes.

Result directories, logs, and generated figures are local run artifacts;
they are not part of the benchmark input collections.

## Additional tools

- [`scripts/python/check_issy_translations.py`](scripts/python/check_issy_translations.py)
  checks translation to Issy, and can compare original and round-trip Issy
  verdicts using an external Issy executable. Use `--list` to preview inputs
  and `--help` for solver and output options.
- [`scripts/process_logs.py`](scripts/process_logs.py) processes evaluation
  logs into CSV and LaTeX summaries.
- [`scripts/cactus.py`](scripts/cactus.py),
  [`scripts/scatter.py`](scripts/scatter.py), and
  [`scripts/tables.py`](scripts/tables.py) generate evaluation plots and tables.
  These scripts expect their evaluation-specific CSV schemas and tool names,
  rather than the single-format runner's CSV schema. Check each script before
  supplying data. Their additional analysis dependencies are listed in
  [`scripts/requirements.txt`](scripts/requirements.txt); use a separate
  analysis environment for that dependency snapshot.

## Comparing consecutive Boolean synthesis inputs

The analysis scripts read saved TLSF rounds and write CSV/JSON summaries, without
copying the TLSF files:

```bash
python benchmarks/scripts/python/analyze_tlsf_additions.py benchmarks/results/BATCH
python benchmarks/scripts/python/analyze_tlsf_line_updates.py benchmarks/results/BATCH
```

The first records pairs that preserve all existing formulas and variables while
adding new ones. The second counts whole formula lines requiring updates as a
fraction of the formulas in the second file, excluding single-file sessions.
Both keep benchmark sessions and base/dual runs separate. See each output's
`summary.json` for the exact comparison rules.
