#!/bin/sh

# Parts of this script were adapted from a
# software artifact available at:
# https://doi.org/10.5281/zenodo.13939202

INPUT=$1
echo "Eval tslmt2rpg [PRUNED] on $INPUT at $(date +%H:%M:%S)"
echo "Run tslmt2rpg at $(date +%H:%M:%S)"
game=$(tslmt2rpg --quiet --prune --rules-disable-precise-deduction --muval-caller call-muval.sh  --muval-timeout 20 < $INPUT) 
echo "Run rpgsolve at $(date +%H:%M:%S)"
res=$(echo "$game" | rpgsolve --disable-log)
echo "$res"