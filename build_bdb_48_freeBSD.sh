#!/bin/sh

# Script to build BDB 4.8 for FreeBSD from:
# https://github.com/BitcoinUnlimited/BitcoinUnlimited/blob/release/doc/build-freebsd.md

# Pick some path to install BDB to, here we create a directory within the bitcoin directory
BDB_PREFIX=$(pwd)/db4
mkdir -p $BDB_PREFIX

# Function for veriry checksum
verify_checksum() {
    file="$1"
    expected_hash="$2"

    echo "${expected_hash}  ${file}" | shasum -a 256 -c - >/dev/null 2>&1
    if [ $? -ne 0 ]; then
        echo "PANIC: Checksum mismatch for file '${file}' — expected SHA-256: ${expected_hash}" >&2
        exit 1
    else
        echo "Checksum OK for file '${file}'"
    fi
}

# Fetch the source and verify that it is not tampered with
curl 'https://download.oracle.com/berkeley-db/db-4.8.30.NC.tar.gz' -o db-4.8.30.NC.tar.gz
verify_checksum db-4.8.30.NC.tar.gz 12edc0df75bf9abd7f82f821795bcee50f42cb2e5f76a6a281b85732798364ef

tar -xzf db-4.8.30.NC.tar.gz

# Fetch, verify that it is not tampered with and apply clang related patch
cd db-4.8.30.NC/
curl 'https://gist.githubusercontent.com/LnL7/5153b251fd525fe15de69b67e63a6075/raw/7778e9364679093a32dec2908656738e16b6bdcb/clang.patch' -o clang.patch
verify_checksum clang.patch 7a9a47b03fd5fb93a16ef42235fa9512db9b0829cfc3bdf90edd3ec1f44d637c
sleep 3
echo "Apply BSD patch"
patch -p2 < clang.patch

# Build the library and install to specified prefix
cd build_unix/
./../dist/configure --enable-cxx --disable-shared --with-pic --prefix=$BDB_PREFIX
gmake install
cd ../..

