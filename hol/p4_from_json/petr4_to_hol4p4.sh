#!/bin/bash

JSON_PATH=$1

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
"$(dirname "$(which Holmake)")/buildheap" --gcthreads=1 --holstate="p4_from_json-heap" petr4_to_hol4p4 "$JSON_PATH" $2 "$arch" "$stf"
exit 0
