#!/bin/bash

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
git clone https://github.com/HOL-Theorem-Prover/HOL.git
cd HOL
git checkout kananaskis-14
poly < tools/smart-configure.sml
bin/build
echo 'export PATH=$PATH:${INSTALL_DIR}/HOL/bin' >> ~/.bashrc
source ~/.bashrc
cd ${CURR_DIR}
