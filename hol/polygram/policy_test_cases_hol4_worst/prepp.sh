
for i in {1..7}; do
    timeout 120s Holmake  "internet_firewall_${i}Theory.uo"
    EXIT_CODE=$?
    if [ $EXIT_CODE -eq 124 ]; then
        echo "TIMEOUT: internet_firewall_${i}Theory.uo exceeded 120s seconds, skipping."
    elif [ $EXIT_CODE -ne 0 ]; then
        echo "FAILED: internet_firewall_${i}Theory.uo exited with code $EXIT_CODE."
    else
        echo " "
    fi
done