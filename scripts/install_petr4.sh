#!/bin/bash
set -euo pipefail

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
git clone https://github.com/verified-network-toolchain/petr4.git
cd petr4
git checkout 0.1.3
#The common includes and the validation tests are taken from the examples of version 0.1.2
"${INSTALL_DIR}/hol/p4_from_json/p4_from_json.sh" fetch-tests "$(pwd)"
sudo apt-get install -y m4 libgmp-dev
# Run this just to be sure
eval $(opam env)
opam install . --deps-only -y
opam pin add p4pp 0.1.12 -y
make
make install
cd ${CURR_DIR}
