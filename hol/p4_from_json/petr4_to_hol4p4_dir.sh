#!/bin/bash
#This script is used to transform all P4 programs in .json representation found in JSONS_PATH to HOL4P4 representation.

JSONS_PATH=$1

# Number of processes - lower to stabilise system
N=$2

# Replace if you want to write to a different log file
log="petr4_to_hol4p4_stf.log"

if [ -f "$log" ] ; then
    rm "$log"
fi

for f in "${JSONS_PATH}"*.json; do
    if [ -s "$f" ]; then
	(
	    echo "Parsing $f..."
	    ./petr4_to_hol4p4.sh "$f" "$log"
	) &

	if [[ $(jobs -r -p | wc -l) -ge $N ]]; then
	    wait -n
	fi
    else
        echo "Warning: $f is empty - did parsing from .p4 to .json fail?"
    fi

done

wait

echo "Done."
