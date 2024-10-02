#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=$1
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/../../binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-rpg-stela-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../rpgsolve
echo "run-rpg-stela.sh with timeout $TIMEOUT" >> $OUTFILE
echo "" >> $OUTFILE

run_rpgstela() {
    echo "Run rpg-stela on $1 at $(date +%H:%M:%S)"
    echo "Benchmark: $1" >> $OUTFILE
    logfile=`mktemp --suffix .log`

    starttime=`date +%s%N`
    result=`PATH=$BASEPATH:$PATH timeout $TIMEOUT $BASEPATH/rpg-stela solve --enable-no-pruning < $1 2> $logfile`
    endtime=`date +%s%N` 
    
    accel_cnt=`cat $logfile | grep 'Accelerated: True' | wc -l`
    
    echo "Runtime: $(((endtime - starttime)/1000000))ms" >> $OUTFILE
    echo "Result: $result" >> $OUTFILE

    echo "" >> $OUTFILE
    rm $logfile
}

for f in `ls $BENCHMARKS_DIR/*.rpg`
do
  run_rpgstela $f
done

for f in `ls $BENCHMARKS_DIR/finite/*.rpg`
do
  run_rpgstela $f
done
