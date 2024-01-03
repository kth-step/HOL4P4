#!/bin/bash

INSTALL_DIR=$1
CURR_DIR=$2

cd ${INSTALL_DIR}
git clone https://github.com/polyml/polyml.git
cd polyml
git checkout v5.9
./configure --prefix=/usr
make
sudo make install
cd ${CURR_DIR}
