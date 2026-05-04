#!/bin/bash

# Compile and build test_bdd_policy
echo "Compiling test_bdd_policy..."
cd ../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S

echo "Building test_bdd_policy executable..."
cd ../bdd_cake_test/ && cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm

echo "Done!"

cd ../policy_test_cases_gen_policy


for i in $(seq 2 2 8); do
    Holmake "internet_firewall_${i}_genTheory.uo"
done
