#!/bin/sh

TSL2TLSF=./opt/tsltools/tsl2tlsf
STRIX=./opt/strix/strix_tlsf.sh

$TSL2TLSF $1.tsl > $1.tlsf
$STRIX $1.tlsf -k -o $1.kiss
