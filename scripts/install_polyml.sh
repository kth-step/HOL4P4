#!/bin/bash

if [[ -z "${POLYML_VERSION}" ]]; then
  POLYML_VERSION="5.9.1"
fi

# If Poly/ML version is 5.7.1, use the one pre-packaged by Ubuntu instead
if [[ "${POLYML_VERSION}" == "5.7.1" ]]; then
  sudo apt install polyml libpolyml-dev
else
#  if [[ ! -e "polyml-${POLYML_VERSION}" ]]; then
    wget https://github.com/polyml/polyml/archive/refs/tags/v${POLYML_VERSION}.tar.gz
    tar -xvf v${POLYML_VERSION}.tar.gz
#  fi
  cd polyml-${POLYML_VERSION}
  ./configure --prefix=/usr
  make
  sudo make install
  cd ..
fi
