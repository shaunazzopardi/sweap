#!/bin/bash


# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=600
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-$TIMESTAMP
LOGFILE=$SCRIPT_DIR/out-$TIMESTAMP.log

runTemos() {
	echo "Run temos on $1 at $(date +%H:%M:%S)" 
	echo "Run temos on $1 at $(date +%H:%M:%S)" >> $OUTFILE
	echo "Benchmark: $1" >> $OUTFILE
	echo "Benchmark: $1" >> $LOGFILE
	tmptsl=`mktemp --suffix .tsl`
	tmptlsf=`mktemp --suffix .tlsf`
	s=`date +%s%N`
	timeout $TIMEOUT $BASEPATH/temos-tslmt2tsl $1 $BASEPATH/cvc5 > $tmptsl 2>> $LOGFILE 
	killall cvc5 2>> $LOGFILE
	timeout $TIMEOUT $BASEPATH/temos-tsl2tlsf $tmptsl > $tmptlsf 2>> $LOGFILE
	INS=$($BASEPATH/syfco -f ltl --print-input-signals $tmptlsf 2>> $LOGFILE)
	OUTS=$($BASEPATH/syfco -f ltl --print-output-signals $tmptlsf 2>> $LOGFILE)
	LTL=$($BASEPATH/syfco -f ltl -q double -m fully $tmptlsf 2>> $LOGFILE)
	timeout $TIMEOUT $BASEPATH/strix --ins "$INS" --outs "$OUTS" -f "$LTL" -r >> $OUTFILE 2>> $LOGFILE
	e=`date +%s%N` 
	echo "Runtime: $(((e - s)/1000000))ms" >> $OUTFILE
	echo "" >> $OUTFILE
	echo "" >> $LOGFILE
        rm $tmptsl $tmptlsf
}

runRpgsolve() {
    echo "Run rpgsolve on $1 at $(date +%H:%M:%S)"
    echo "Run rpgsolve on $1 at $(date +%H:%M:%S)" >> $OUTFILE
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

TEMOS_DIR=examples/benchmarks/temos
for f in `ls $TEMOS_DIR`
do
  runTemos $TEMOS_DIR/$f
done

RPGSOLVE_DIR=examples/benchmarks/rpgsolve
for f in `ls $RPGSOLVE_DIR/*.rpg`
do
  runRpgsolve $RPGSOLVE_DIR/$f
done
