#!/bin/bash

output=$( refines --brief --quiet fdr/examples.csp 2>&1 | tee /dev/tty )

if echo $output | grep -q 'Failed'; then
    echo "At least one assertion failed";
    exit -1;
fi