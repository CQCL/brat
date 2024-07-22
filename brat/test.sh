#!/bin/bash

BRAT=~/.local/bin/brat

FIX=0
PIX=0
declare -a FAILURES
declare -a PASSES

function die() {
    echo "Failed to check " $1
    exit 1
}

for i in examples/*.brat; do
    $BRAT $i >/dev/null 2>&1
    if [ 0 -eq $? ];
    then
        PASSES[$PIX]="$i"
        PIX=$(($PIX+1))
    else
        FAILURES[$FIX]="$i"
        FIX=$(($FIX+1))
    fi
done

echo Passes
for i in ${PASSES[*]}; do
    echo "> " $i
done
echo ""
echo Failures
for i in ${FAILURES[*]}; do
    echo "> " $i
done
