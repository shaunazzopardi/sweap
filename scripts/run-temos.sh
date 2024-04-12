#!/bin/bash

# Parts of this script were adapted from a
# software artifact available at:
# https://zenodo.org/doi/10.5281/zenodo.8409938

TIMEOUT=600
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
BASEPATH=$SCRIPT_DIR/../binaries
TIMESTAMP=`date +%Y-%m-%d-%H-%M-%S`
OUTFILE=$SCRIPT_DIR/out-temos-$TIMESTAMP
LOGFILE=$SCRIPT_DIR/log-temos-$TIMESTAMP
BENCHMARKS_DIR=$SCRIPT_DIR/../examples/benchmarks/temos

run_temos() {
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
	timeout $TIMEOUT $BASEPATH/strix --ins "$INS" --outs "$OUTS" -f "$LTL" -r | grep 'REAL' >> $OUTFILE 2>> $LOGFILE
	e=`date +%s%N` 
	echo "Runtime: $(((e - s)/1000000))ms" >> $OUTFILE
	echo "" >> $OUTFILE
	echo "" >> $LOGFILE
        rm $tmptsl $tmptlsf
}

for f in `ls $BENCHMARKS_DIR/*.tslt`
do
  run_temos $f
done

#for f in `ls $RPGSOLVE_DIR/*.rpg`
#do
  #runRpgsolve $f
#done

#oldpath=$PWD
#cd $BASEPATH
#for f in `ls $SCRIPT_DIR/$RABONIEL_DIR/*.tslmt`
#do
  #runRaboniel $f
#done
#cd $oldpath
