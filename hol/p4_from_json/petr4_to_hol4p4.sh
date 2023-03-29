#!/bin/bash

set -e
"$(dirname "$(which Holmake)")/buildheap" --gcthreads=1 --holstate="p4_from_json-heap" petr4_to_hol4p4 $1 $2
exit 0
