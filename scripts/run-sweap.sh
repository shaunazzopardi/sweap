#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=600
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/..
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-sweap-$TIMESTAMP
LOGFILE=$SCRIPT_DIR/log-sweap-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../examples/benchmarks/sweap

run_sweap() {
	echo "Run Sweap on  $1 at $(date +%H:%M:%S)" 
	echo "Run Sweap on  $1 at $(date +%H:%M:%S)" >> $OUTFILE
	echo "$1" >> $OUTFILE
	s=`date +%s%N`
        PATH=$BASEPATH/binaries:$PATH PYTHONPATH=$BASEPATH/src/ timeout $TIMEOUT python3 $BASEPATH/main.py --synthesise  --p $1  2> $LOGFILE | grep "^\(Unr\|R\)ealizable\." >> $OUTFILE 
	e=`date +%s%N` 
	echo "Runtime: $(((e - s)/1000000))ms" >> $OUTFILE
	echo "" >> $OUTFILE
}


for f in `ls $BENCHMARKS_DIR/*.prog`
do
  run_sweap $f
done