#!/bin/bash
#This script is used as a quick-and-dirty way to install all prerequisites and compile HOL4P4 on a fresh Ubuntu 22.04 installation.

sudo apt-get update
sudo apt-get install -y build-essential git python3 file

#Path to where this file is located
FILE=$(readlink -f "$0")
FILEPATH=$(dirname "$FILE")

#TODO Check if Poly/ML is correct version by using "poly -v". Give choice: use old, or overwrite with new.

. ${FILEPATH}/install_polyml.sh ${PWD} ${PWD}

#TODO Check if HOL4 is installed by using "which Holmake"
#TODO Ask if ~/.bashrc should be written to
#TODO Double-check that the line writing to .bashrc writes the correct directory

. ${FILEPATH}/install_hol4.sh ${PWD} ${PWD}

#TODO Tested with OCaml 4.13.1 - fix version?
#. ${FILEPATH}/install_opam.sh

#. ${FILEPATH}/install_ott.sh

#. ${FILEPATH}/install_petr4.sh ${FILEPATH}/.. ${PWD}


