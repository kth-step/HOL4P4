#!/bin/bash

# Compile and build test_bdd_policy
echo "Compiling test_bdd_policy..."
cd ../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S

echo "Building test_bdd_policy executable..."
cd ../bdd_cake_test/ && cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm

echo "Done!"

cd ../reviewers_test_here



for target in \
    "paper_example_cakeml_bestTheory.uo" \
    "paper_example_cakeml_worstTheory.uo" \
    "paper_example_hol4_worstTheory.uo" \
    "paper_example_hol4_bestTheory.uo"; do
    echo "Running Holmake $target..."
    Holmake "$target"
done
