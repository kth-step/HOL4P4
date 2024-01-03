#!/bin/bash

sudo apt-get install -y opam
opam init -y
eval $(opam env --switch=default)
