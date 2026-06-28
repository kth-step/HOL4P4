#!/usr/bin/env bash

set -euo pipefail

# TODO: Clean-up
URL="https://github.com/CakeML/cakeml/releases/download/vHOL-Trindemossen-2/cake-x64-64.tar.gz"
ARCHIVE_NAME="cake-x64-64.tar.gz"
DEST_DIR="cake-x64-64"

WORKDIR="$(pwd)"
ARCHIVE_PATH="${WORKDIR}/${ARCHIVE_NAME}"

if command -v curl >/dev/null 2>&1; then
    curl -L --fail -o "${ARCHIVE_PATH}" "${URL}"
elif command -v wget >/dev/null 2>&1; then
    wget -O "${ARCHIVE_PATH}" "${URL}"
else
    echo "Error: neither curl nor wget is installed. Install one and re-run." >&2
    exit 1
fi

tar -xzf "${ARCHIVE_PATH}"
cp -f "${WORKDIR}/basis_ffi.c" "${DEST_DIR}/basis_ffi.c"
cp -rf "${DEST_DIR}/." "${WORKDIR}/"

# Clean-up
rm -f "${ARCHIVE_PATH}"
rm -rf "${WORKDIR}/${DEST_DIR}"

# Link the CakeML compiler
make cake
