#!/bin/bash
#This script takes a .json file exported by petr4 (JSON_PATH) and a path to a log file (LOG_PATH),
#then uses petr4_to_hol4p4 to transform the the program in .json representation for symbolic execution.

JSON_PATH=$1
LOG_PATH=$2

if [ "$#" -ne 2 ]; then
    echo "petr4_to_hol4p4.sh requires two arguments: the first a path to a P4 program in petr4 JSON format, the second a path to a log file."
    exit 1
fi


# Whether to strip the .json files of debug information (file and line of code of element, et.c.)
# This makes it a lot faster to process, but also removes the information for later use
remove_debug=true

if [ "$remove_debug" = true ] ; then
    ./strip_json_info.sh "$JSON_PATH"
fi

arch=$(./petr4_get_arch.sh "${JSON_PATH%.json}.p4")

if [ "$arch" = "none" ]; then
    echo "No architecture found in the associated .p4 file. Check that your P4 program uses a proper architecture, or adapt petr4_get_arch.sh to recognize the right architecture."
    exit 1
fi

mode="symbolic"

set -e
"$(dirname "$(which Holmake)")/buildheap" --gcthreads=1 --holstate="p4_from_json-heap" petr4_to_hol4p4 "$JSON_PATH" "$LOG_PATH" "$arch" "$mode"
exit 0
