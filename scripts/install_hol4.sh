#!/bin/bash

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
git clone https://github.com/HOL-Theorem-Prover/HOL.git
cd HOL
git checkout kananaskis-14
# Add compilation flags to avoid ISO C++17 incompatibility errors
sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' src/HolSat/sat_solvers/minisat/Makefile
sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' src/HolSat/sat_solvers/zc2hs/Makefile
poly < tools/smart-configure.sml
bin/build
# For bash
echo 'export PATH=$PATH:${INSTALL_DIR}/HOL/bin' >> ~/.bashrc
source ~/.bashrc
# As environment variable
#sed -i "s|\(PATH=[\"].*\)[\"]|\1:$INSTALL_DIR/HOL/bin\"|" /etc/environment
cd ${CURR_DIR}
