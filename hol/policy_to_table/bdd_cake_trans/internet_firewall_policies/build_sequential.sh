#!/bin/bash
for file in *Script.sml; do
    base=$(basename "$file" Script.sml)
    Holmake "${base}Theory.uo"
done