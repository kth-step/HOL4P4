#!/bin/bash
#This script is used to transform .p4 programs to a .json representation using petr4.

#Note that this argument should end with a slash
EXAMPLES_PATH=$1
P4_INCLUDE=$2

for f in "${EXAMPLES_PATH}"*.p4; do petr4 typecheck -json -I "${P4_INCLUDE}" "$f" > "${f%.p4}.json"; done
