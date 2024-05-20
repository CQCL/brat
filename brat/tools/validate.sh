#!/bin/bash

set -u

if ! which hugr_validator; then
    "hugr_validator not found in path"
    exit 1
fi

declare -a FAILED_TEST_NAMES
declare -a FAILED_TEST_MSGS
NUM_FAILURES=0

for json in test/compilation/output/*.json; do
    echo Validating $json
    RESULT=$(cat $json | hugr_validator 2>&1)
    if [ $? -ne 0 ]; then
        FAILED_TEST_NAMES[$NUM_FAILURES]=$json
        FAILED_TEST_MSGS[$NUM_FAILURES]=$RESULT
        NUM_FAILURES=$(($NUM_FAILURES + 1))
    fi
done

RED='\033[0;31m'
GREEN='\033[0;32m'
NO_COLOUR='\033[0m'

if [ $NUM_FAILURES -gt 0 ]; then
    echo -e $RED
    for ix in $(seq 0 $(($NUM_FAILURES - 1))); do
        echo "Validation failed: " ${FAILED_TEST_NAMES[$ix]}
        echo $FAILED_TEST_MSGS[$ix]
    done

    echo $NUM_FAILURES failures. $NO_COLOUR
    exit 1
else
    echo -e $GREEN All tests passed $NO_COLOUR
    exit 0
fi
