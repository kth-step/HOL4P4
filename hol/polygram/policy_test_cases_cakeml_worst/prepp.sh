#!/bin/bash

# Compile and build test_bdd_policy
echo "Compiling test_bdd_policy..."
cd ../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S

echo "Building test_bdd_policy executable..."
cd ../bdd_cake_test/ && cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm

# Compile and build test_bdd_table
echo "Compiling test_bdd_table..."
cd ../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_table.sexp > test_bdd_table.cake.S

echo "Building test_bdd_table executable..."
cd ../bdd_cake_test/ && cc test_bdd_table.cake.S basis_ffi.c -lm -o test_bdd_table.cake -lm

echo "Done!"

cd ../policy_test_cases_cakeml_worst



for i in {1..7}; do
    timeout 20s Holmake "internet_firewall_${i}Theory.uo"
    EXIT_CODE=$?
    if [ $EXIT_CODE -eq 124 ]; then
        echo "TIMEOUT: internet_firewall_${i}Theory.uo exceeded 20s seconds, skipping."
    elif [ $EXIT_CODE -ne 0 ]; then
        echo "FAILED: internet_firewall_${i}Theory.uo exited with code $EXIT_CODE."
    else
        echo " "
    fi
done