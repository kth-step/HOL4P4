#!/bin/bash

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
#If Holmake already exists, don't re-build HOL
if [ ! -e "HOL/bin/Holmake" ]; then
	git clone https://github.com/HOL-Theorem-Prover/HOL.git
	cd HOL
	git checkout trindemossen-1
	# Add compilation flags to avoid ISO C++17 incompatibility errors
	# Note: Only done for amd64, doing this patch on aarch64 results in worse errors
	if [[ $(dpkg --print-architecture) == "amd64" ]]
	then
		sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' src/HolSat/sat_solvers/minisat/Makefile
		sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' src/HolSat/sat_solvers/zc2hs/Makefile
	fi
	if [[ "${POLYML_VERSION}" == "5.7.1" ]]; then
	  echo "val polymllibdir = \"/usr/lib/x86_64-linux-gnu\";" > tools-poly/poly-includes.ML
	fi
	poly < tools/smart-configure.sml
	bin/build
	# For bash
	echo 'export PATH=$PATH:${INSTALL_DIR}/HOL/bin' >> ~/.bashrc
	source ~/.bashrc
	# As environment variable
	#sed -i "s|\(PATH=[\"].*\)[\"]|\1:$INSTALL_DIR/HOL/bin\"|" /etc/environment
else
	echo 'export PATH=$PATH:${INSTALL_DIR}/HOL/bin' >> ~/.bashrc
	source ~/.bashrc
fi
cd ${CURR_DIR}
