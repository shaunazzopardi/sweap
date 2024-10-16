#!/usr/bin/env bash

BASEPATH=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
tmptsl=`mktemp --suffix .tsl`
tmptlsf=`mktemp --suffix .tlsf`
$BASEPATH/temos-tslmt2tsl $1 $BASEPATH/cvc5 > $tmptsl
killall cvc5
$BASEPATH/temos-tsl2tlsf $tmptsl > $tmptlsf
rm $tmptsl
INS=$($BASEPATH/syfco -f ltl --print-input-signals $tmptlsf)
OUTS=$($BASEPATH/syfco -f ltl --print-output-signals $tmptlsf)
LTL=$($BASEPATH/syfco -f ltl -q double -m fully $tmptlsf)
$BASEPATH/strix --ins "$INS" --outs "$OUTS" -f "$LTL" -r
rm $tmptlsf