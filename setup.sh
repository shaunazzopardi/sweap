#!/usr/bin/env bash
set -e

# Run from the repository root with your virtual environment activated.
python -m pip install -r requirements.txt
python -m pysmt install --msat
# z3-solver is installed by requirements.txt; pySMT's installer pins an older Z3.
python -m pysmt install --bdd
