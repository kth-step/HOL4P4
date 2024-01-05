#!/bin/bash

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
git clone https://github.com/verified-network-toolchain/petr4.git
cd petr4
#First, copy the includes and validation tests from version 0.1.2
git checkout 0.1.2

#Includes
#TODO: VSS also?
mkdir -p ${INSTALL_DIR}/hol/p4_from_json/p4include;
cp examples/core.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/
cp examples/ebpf_model.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/
cp examples/v1model.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/

#Skeleton files
cp examples/checker_tests/good/arith-inline-skeleton.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/
cp examples/checker_tests/good/arith-skeleton.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/
cp examples/checker_tests/good/ebpf_headers.p4 ${INSTALL_DIR}/hol/p4_from_json/p4include/

#Copy over only those .p4 test files which have an accompanying .stf file
for file in ./examples/checker_tests/good/*.stf; do
    filename=$(basename "${file%.stf}") 
    cp ./examples/checker_tests/good/${filename}.stf ${INSTALL_DIR}/hol/p4_from_json/validation_tests/
    cp ./examples/checker_tests/good/${filename}.p4 ${INSTALL_DIR}/hol/p4_from_json/validation_tests/
done

#Then, checkout version 0.1.3 and use it afterward
git checkout 0.1.3
sudo apt-get install -y m4 libgmp-dev
opam install . --deps-only -y
opam pin add p4pp 0.1.12 -y
make
make install
cd ${CURR_DIR}
