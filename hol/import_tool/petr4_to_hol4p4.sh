#!/bin/bash
#This script takes a directory containing .json files exported by petr4 (JSON_PATH) and a path to a log file (LOG_PATH),
#then uses petr4_to_hol4p4 to transform the all programs in .json format found in JSON_PATH into HOL4P4 format.

JSON_PATH=$1
LOG_PATH=$2

if [ "$#" -ne 2 ]; then
    echo "petr4_to_hol4p4.sh requires two arguments: the first a path to a P4 program in petr4 JSON format, the second a path to a log file"
    exit 1
fi


# Whether to strip the .json files of debug information (file and line of code of element, et.c.)
# This makes it a lot faster to process, but also removes the information for later use
remove_debug=true

if [ "$remove_debug" = true ] ; then
    ./strip_json_info.sh "$JSON_PATH"
fi

arch=$(./petr4_get_arch.sh "${JSON_PATH%.json}.p4")

# Check if .stf file exists
if [ -e "${JSON_PATH%.json}.stf" ]; then
    stf="Y"
else
    stf="N"
fi

set -e
"$(dirname "$(which Holmake)")/buildheap" --gcthreads=1 --holstate="import_tool-heap" petr4_to_hol4p4 "$JSON_PATH" "$LOG_PATH" "$arch" "$stf"
exit 0
