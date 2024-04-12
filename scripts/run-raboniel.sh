#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=600
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/../binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-raboniel-$TIMESTAMP
LOGFILE=$SCRIPT_DIR/log-raboniel-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../examples/benchmarks/raboniel

run_raboniel() {
	echo "Run raboniel on $1 at $(date +%H:%M:%S)" 
	echo "Run raboniel on $1 at $(date +%H:%M:%S)" >> $OUTFILE
	echo "Benchmark: $1" >> $OUTFILE
	echo "Benchmark: $1" >> $LOGFILE
	s=`date +%s%N`
	timeout $TIMEOUT ./raboniel --spec $1 2>> $LOGFILE | grep 'Result' >> $OUTFILE
	e=`date +%s%N` 
	echo "Runtime: $(((e - s)/1000000))ms" >> $OUTFILE
	echo "" >> $OUTFILE
	echo "" >> $LOGFILE
}


oldpath=$PWD
cd $BASEPATH
for f in `ls $BENCHMARKS_DIR/*.tslmt`
do
  run_raboniel $f
done
for f in `ls $BENCHMARKS_DIR/finite/*.tslmt`
do
  run_raboniel $f
done
cd $oldpath
