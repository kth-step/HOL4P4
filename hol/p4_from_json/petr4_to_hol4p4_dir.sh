#!/bin/bash

JSONS_PATH=$1

# Number of processes - lower to stabilise system
N=8

# Replace if you want to write to a different log file
log="petr4_to_hol4p4.log"

if [ -f "$log" ] ; then
    rm "$log"
fi

for f in "${JSONS_PATH}"*.json; do
    if [ -s "$f" ]; then
	(
	    echo "Parsing $f..."
	    ./petr4_to_hol4p4.sh "$f" "$log" > "${f%.json}Script.sml"
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
