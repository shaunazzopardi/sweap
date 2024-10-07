#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=$1
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/../../binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-rpgsolve-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../rpgsolve
echo "run-rpgsolve.sh with timeout $TIMEOUT" >> $OUTFILE
echo "" >> $OUTFILE

run_rpgsolve() {
    name=`basename $1`
    echo "Run rpgsolve on $1 at $(date +%H:%M:%S)"
    echo "Benchmark: $1" >> $OUTFILE
    logfile=`mktemp --suffix .log`

    starttime=`date +%s%N`
    result=`timeout $TIMEOUT $BASEPATH/rpgsolve < $1 2> $logfile`
    endtime=`date +%s%N` 
    
    killall z3 2> /dev/null

    accel_cnt=`cat $logfile | grep 'Accelerated: True' | wc -l`
    
    echo "Runtime: $(((endtime - starttime)/1000000))ms" >> $OUTFILE
    echo "Result: $result" >> $OUTFILE
    echo "Sucessfull Accelerations: $accel_cnt" >> $OUTFILE

    echo "" >> $OUTFILE
    rm $logfile
}

for f in `ls $BENCHMARKS_DIR/*.rpg`
do
  run_rpgsolve $f
done

