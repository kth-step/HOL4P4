#!/bin/bash

wget https://github.com/polyml/polyml/archive/refs/tags/v5.9.1.tar.gz
tar -xvf v5.9.1.tar.gz
cd polyml-5.9.1
./configure --prefix=/usr
make
sudo make install
cd ..
