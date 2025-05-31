#!/bin/sh -v
# Needed install from ports or pkg:
#	devel/libevent
#	devel/boost-libs
#	databases/db48
#       openssl
# and build tools:
#       autoconf
#       automake
#       libtool
#       pkgconf
#       gmake
#
# With pkg, use the command:
#   pkg install autoconf automake libtool pkgconf gmake libevent boost-libs openssl
#
# Build Berkeley DB 4.8 with local script:
# ./build_bdb_48_freeBSD.sh
# Or use configure option "non-compatible wallet"

# Generate configure file once, before run this script:
# ./autogen.sh

BDB_PREFIX=$(pwd)/db4
CPPFLAGS="-I${BDB_PREFIX}/include -I/usr/local/include"
LDFLAGS="-L${BDB_PREFIX}/lib -L/usr/local/lib"
CFLAGS=$CPPFLAGS
CXXFLAGS=$CPPFLAGS

export LDFLAGS CPPFLAGS CFLAGS CXXFLAGS

#./configure --disable-tests --disable-dependency-tracking
#./configure --enable-debug --disable-dependency-tracking
#./configure --enable-debug --with-libs
#./configure --disable-tests --enable-debug  --disable-util-tx --disable-gui-tests --enable-bip70 --disable-dependency-tracking
./configure --disable-tests --enable-debug  --disable-util-tx --disable-gui-tests --disable-dependency-tracking
