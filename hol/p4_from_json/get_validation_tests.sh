#!/bin/bash
#This script downloads the validation tests if you somehow missed that part during installation.

#Path to where this file is located
FILE=$(readlink -f "$0")
FILEPATH=$(dirname "$FILE")

cd ${FILEPATH}
git clone https://github.com/verified-network-toolchain/petr4.git
cd petr4
#Copy the includes and validation tests from version 0.1.2
git checkout 0.1.2

#Includes
#TODO: VSS also?
mkdir -p ../p4include;
cp examples/core.p4 ../p4include/
cp examples/ebpf_model.p4 ../p4include/
cp examples/v1model.p4 ../p4include/

#Skeleton files
cp examples/checker_tests/good/arith-inline-skeleton.p4 ../p4include/
cp examples/checker_tests/good/arith-skeleton.p4 ../p4include/
cp examples/checker_tests/good/ebpf_headers.p4 ../p4include/

#Validation tests: copy over only those .p4 test files which have an accompanying .stf file
mkdir -p ../validation_tests;
for file in ./examples/checker_tests/good/*.stf; do
    filename=$(basename "${file%.stf}") 
    cp ./examples/checker_tests/good/${filename}.stf ../validation_tests/
    cp ./examples/checker_tests/good/${filename}.p4 ../validation_tests/
done
cd ..
rm -rf petr4
echo "Deleted petr4 repository"
