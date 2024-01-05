#!/bin/bash
#This script is the second part of the installation script

#Path to where this file is located
FILE=$(readlink -f "$0")
FILEPATH=$(dirname "$FILE")

#TODO Tested with OCaml 4.13.1 - fix version?
. ${FILEPATH}/install_opam.sh

. ${FILEPATH}/install_ott.sh

. ${FILEPATH}/install_petr4.sh ${FILEPATH}/.. ${PWD}


