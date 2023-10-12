#!/bin/bash
#This script is used to deduce which architecture a P4 program belongs to, based on its includes.

if grep -q "#include <ebpf_model.p4>" "$1"; then
    echo "ebpf"
elif grep -q "#include \"very_simple_model.p4\"" "$1"; then
    echo "vss"
elif grep -q "#include <v1model.p4>" "$1"; then
    echo "v1model"
fi
