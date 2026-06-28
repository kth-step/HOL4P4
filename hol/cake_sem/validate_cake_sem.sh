#!/bin/bash
#Note that this script relies on petr4.

if [ $# -eq 0 ]; then
    NTHREADS=1
else
    NTHREADS=$1
fi

./../p4_from_json/petr4_json_export.sh validation_tests/ p4include/

./../p4_from_json/petr4_to_hol4p4_dir.sh validation_tests/ ${NTHREADS} hol4p4exe_stf

cd validation_tests

Holmake

cd ..
