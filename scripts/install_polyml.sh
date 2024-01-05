#!/bin/bash

git clone https://github.com/polyml/polyml.git
cd polyml
git checkout v5.9
./configure --prefix=/usr
make
sudo make install
cd ..
