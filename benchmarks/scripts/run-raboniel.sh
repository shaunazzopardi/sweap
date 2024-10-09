#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=$1
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/../../binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-raboniel-$TIMESTAMP
LOGFILE=$SCRIPT_DIR/log-raboniel-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../raboniel
echo "run-raboniel.sh with timeout $TIMEOUT" >> $OUTFILE
echo "" >> $OUTFILE

run_raboniel() {
    name=`basename $1`
    echo "Run raboniel on $1 at $(date +%H:%M:%S)"
    echo "Benchmark: $name" >> $OUTFILE
    echo "Benchmark: $name" >> $LOGFILE
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
