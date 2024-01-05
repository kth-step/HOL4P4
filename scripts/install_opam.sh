#!/bin/bash

sudo apt-get install -y opam
opam init --auto-setup --yes --disable-sandboxing
eval $(opam env --switch=default)
