#!/bin/bash

BRAT=~/.local/bin/brat

# List the files we expect to fail.
XFAILS="composition.brat
        juxt.brat
        karlheinz.brat
        karlheinz_alias.brat
        kernel.brat
        listpair.brat
        thin.brat
        hea.brat"

declare -a FAILURES
declare -a PASSES
declare -a XFAILED

cd examples

for i in *.brat; do
    (echo " $XFAILS" | grep " $i" > /dev/null)
    XFAIL=$?  # Result code whether this file was in the list or not.
    if ($BRAT $i >/dev/null 2>&1); then
        if [ 0 -eq $XFAIL ]; then
            i="(PASS) $i"  # Unexpected pass (but allowed)
        fi
        PASSES+=("$i")
    else
        if [ 0 -eq $XFAIL ]; then
            XFAILED+=("$i")
        else
            FAILURES+=("$i")
        fi
    fi
done

echo Passes
for i in "${PASSES[@]}"; do
    echo "> $i"
done
echo
echo "Expected failures (XFAILs)"
for i in "${XFAILED[@]}"; do
  echo "> $i"
done
echo
if [ 0 -ne ${#FAILURES[@]} ]; then
  echo "There were test failures:"
  for i in "${FAILURES[@]}"; do
    echo "> $i"
  done
  exit 1
fi
