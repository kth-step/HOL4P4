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

cd ../policy_test_cases_length_rule

for i in {10..10}; do
    Holmake "internet_firewall_10_${i}Theory.uo"
done
