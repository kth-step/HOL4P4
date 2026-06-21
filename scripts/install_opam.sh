#!/bin/bash

sudo apt-get install -y opam
opam init --auto-setup --yes --disable-sandboxing --compiler=4.13.1
eval $(opam env --switch=default)
