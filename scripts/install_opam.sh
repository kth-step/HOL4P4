#!/bin/bash
set -euo pipefail

sudo apt-get install -y opam
# OCaml 4.13.1 does not compile as C23, the default of GCC 15
CC="gcc -std=gnu17" opam init --auto-setup --yes --disable-sandboxing --compiler=4.13.1
eval $(opam env)
