#!/bin/bash

progname=$1

if [ -z $1 ]; then
  echo "Usage: supply the name of the CakeML sexp file without the .sexp suffix as a command-line argument"
  exit 0
fi

# NOTE: Always set skip_type_inference to false if you don't know what you're doing when in-lining CakeML code.
CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=true --emit_empty_ffi=true --reg_alg=0 < $progname.sexp > $progname.cake.S

cc ${progname}.cake.S basis_ffi.c -o ${progname}.cake
