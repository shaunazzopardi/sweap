#!/usr/bin/env bash

# Use the bundled converter even when called without the repository on PATH.
binary_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)" || exit 1

# Usage: strix_tlsf_file.sh INPUT.tlsf [STRIX_OPTIONS...]
TLSF="${1:-}"
if [[ -z "$TLSF" ]]; then
    echo "Error: No TLSF file given" >&2
    exit 1
fi
shift
OPTIONS=("$@")
if [[ ! -f "$TLSF" ]]; then
    echo "Error: File $TLSF does not exist" >&2
    exit 1
fi

ltl_file=$(mktemp "${TMPDIR:-/tmp}/sweap-strix.XXXXXXXXXX") || exit 1
trap 'rm -f -- "$ltl_file"' EXIT

INS=$("$binary_dir/syfco" -f ltl --print-input-signals "$TLSF") || exit "$?"
OUTS=$("$binary_dir/syfco" -f ltl --print-output-signals "$TLSF") || exit "$?"
"$binary_dir/syfco" -f ltl -q double -m fully "$TLSF" > "$ltl_file" || exit "$?"

strix --ins "$INS" --outs "$OUTS" --formula-file "$ltl_file" "${OPTIONS[@]}"
