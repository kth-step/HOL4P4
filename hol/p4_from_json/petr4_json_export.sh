#!/bin/bash

#Note that this argument should end with a slash
EXAMPLES_PATH=$1
P4_INCLUDE=~/Documents/my-projects/P4/p4ott/hol/p4_from_json/test-examples/p4include

for f in "${EXAMPLES_PATH}"*.p4; do petr4 typecheck -json -I "${P4_INCLUDE}" "$f" > "${f%.p4}.json"; done
