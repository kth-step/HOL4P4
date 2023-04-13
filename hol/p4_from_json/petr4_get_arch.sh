#!/bin/bash

if grep -q "#include <ebpf_model.p4>" "$1"; then
    echo "ebpf"
elif grep -q "#include \"very_simple_model.p4\"" "$1"; then
    echo "vss"
fi
