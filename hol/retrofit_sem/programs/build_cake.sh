#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: $0 <program_name>"
    echo "Example: $0 port_swap"
    exit 1
fi

PROGRAM_NAME=$1

Holmake ${PROGRAM_NAME}Theory

cp ${PROGRAM_NAME}.sexp compilation/

cd compilation

./compile_cake.sh ${PROGRAM_NAME}

cd ..
