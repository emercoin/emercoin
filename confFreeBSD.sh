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
#   pkg install autoconf automake libtool pkgconf gmake libevent boost-libs db48 openssl

CPPFLAGS='-I/usr/local/include/db48/ -I/usr/local/include'
LDFLAGS='-L/usr/local/lib/db48/ -L/usr/local/lib'
CFLAGS=$CPPFLAGS
CXXFLAGS=$CPPFLAGS

export LDFLAGS CPPFLAGS CFLAGS CXXFLAGS

#./configure --disable-tests --disable-dependency-tracking
#./configure --enable-debug --disable-dependency-tracking
#./configure --enable-debug --with-libs
#./configure --disable-tests --enable-debug  --disable-util-tx --disable-gui-tests --enable-bip70 --disable-dependency-tracking
./configure --disable-tests --enable-debug  --disable-util-tx --disable-gui-tests --disable-dependency-tracking
