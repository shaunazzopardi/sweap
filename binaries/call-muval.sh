#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
COARDIR=$SCRIPT_DIR
BINARY=$COARDIR/muval
OLDDIR=$(pwd)
INFILE=$(mktemp --suffix=.hes)

OPTS="-c $COARDIR/config/solver/dbg_muval_parallel_exc_tb_ar.json -p muclp"

TIMEOUT=$1

tee > $INFILE

cd $COARDIR
timeout $TIMEOUT systemd-run --scope -p MemoryMax=8G --user $BINARY $OPTS $INFILE 2> /dev/null
cd $OLDDIR

rm $INFILE
