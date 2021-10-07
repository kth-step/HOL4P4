#!/usr/bin/env bash

# Exit immediately if an error happens
set -e

# Create the cache if it doesn't exist yet
mkdir -p /home/runner/cache

# Location of Github Actions cache 
CACHE_DIR=/home/runner/cache

# Based on HOL4 developers/install-poly.sh
POLYML_BASE="https://github.com/polyml/polyml"
POLYML_URL=${POLYML_BASE}/archive/${POLYML_VERSION}.tar.gz
POLYML_DIR=${CACHE_DIR}/polyml_${POLYML_VERSION}
POLYML_DIR_SRC=${CACHE_DIR}/polyml_${POLYML_VERSION}_src

# If the output directory exists, we already have a Poly/ML in the cache
if [[ -d "${POLYML_DIR}" ]]; then
  echo "Poly/ML is already available in the cache, exiting."
  exit 0
else
  echo "Poly/ML is not in the cache, downloading it now."
fi

# Create Poly/ML source and binary directories
mkdir "${POLYML_DIR_SRC}"
mkdir "${POLYML_DIR}"

# Download Poly/ML source
wget -qO- ${POLYML_URL} | \
  tar xvz -C "${POLYML_DIR_SRC}" --strip-components 1

# Compile Poly/ML
cd "${POLYML_DIR_SRC}"
echo "*** Configuring Poly/ML for prefix: ${POLYML_DIR}"
./configure --prefix="${POLYML_DIR}"
make

# Install Poly/ML to directory provided in prefix flag above
make install

# Remove the source directory
cd ${CACHE_DIR}
rm -rf "${POLYML_DIR_SRC}"

