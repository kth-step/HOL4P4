#!/bin/bash

set -e
"$(dirname "$(which Holmake)")/buildheap" --gcthreads=1 --holstate="p4_from_json-heap" parse_any_test $1 $2
exit 0
