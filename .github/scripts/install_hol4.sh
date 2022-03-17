#!/usr/bin/env bash

# Exit immediately if an error happens
set -e

# Location of Github Actions cache 
CACHE_DIR=/home/runner/cache

# Poly/ML directory (TODO: Save from earlier?)
POLYML_DIR=${CACHE_DIR}/polyml_${POLYML_VERSION}

# HOL4 Github repository and release branch
GIT_URL=https://github.com/HOL-Theorem-Prover/HOL.git
HOL4_DIR=${CACHE_DIR}/hol4_${HOL4_VERSION}

# Add path variables needed for HOL4 installation
export PATH=${POLYML_DIR}/bin:$PATH
export LD_LIBRARY_PATH=${POLYML_DIR}/lib:$LD_LIBRARY_PATH

cd ${CACHE_DIR}
if [[ -d "${HOL4_DIR}" ]]; then
  echo "HOL4 is already available in the cache."
  exit 0
else
  echo "HOL4 is not in the cache, downloading it now."
  # .. clone the specified HOL4 branch only ...
  git clone -b ${HOL4_VERSION} --single-branch ${GIT_URL} "${HOL4_DIR}"
  # ... and compile HOL4.
  cd "${HOL4_DIR}"
  poly < tools/smart-configure.sml
  bin/build --nograph
fi
cd ${CACHE_DIR}

