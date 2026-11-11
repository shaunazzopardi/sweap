#!/usr/bin/env bash

# Use the bundled converter even when called without the repository on PATH.
binary_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

#parse command line arguments
OPTIONS=()

while [[ $# -gt 0 ]]
do
key="$1"

if [[ $key = *.tlsf ]]; then
    # tlsf file
    TLSF=$1
else
    # option
    OPTIONS+=("$1")
fi
# next argument
shift

done

if [ -z $TLSF ]; then
    echo "Error: No TLSF file given"
    exit 1
fi
if [ ! -f $TLSF ]; then
    echo "Error: File $TLSF does not exist"
    exit 1
fi

ltlfile=$(mktemp) 
INS=$("$binary_dir/syfco" -f ltl --print-input-signals "$TLSF")
OUTS=$("$binary_dir/syfco" -f ltl --print-output-signals "$TLSF")
LTL=$("$binary_dir/syfco" -f ltl -q double -m fully "$TLSF" -o "$ltlfile")

strix --ins "$INS" --outs "$OUTS" -F "$ltlfile" ${OPTIONS[@]}
rm -f $ltlfile

