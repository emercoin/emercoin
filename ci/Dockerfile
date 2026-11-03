# CI and build image: Ubuntu 18.04 + gcc 8, the toolchain of the release builds
# (contrib/gitian-descriptors/gitian-linux.yml, gitian-win.yml).
# Hosts: x86_64-linux-gnu (native), aarch64-linux-gnu, x86_64-w64-mingw32 (posix threads).
FROM ubuntu:18.04

ENV DEBIAN_FRONTEND=noninteractive TZ=UTC LC_ALL=C.UTF-8 LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential gcc-8 g++-8 libtool autotools-dev automake autoconf \
        pkg-config bsdmainutils curl ca-certificates git python3 python3-zmq \
        patch xz-utils zip nsis \
        g++-8-aarch64-linux-gnu gcc-8-aarch64-linux-gnu binutils-aarch64-linux-gnu \
        g++-mingw-w64-x86-64 binutils-mingw-w64-x86-64 \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 80 \
                           --slave /usr/bin/g++ g++ /usr/bin/g++-8 \
    && ln -s /usr/bin/aarch64-linux-gnu-gcc-8 /usr/local/bin/aarch64-linux-gnu-gcc \
    && ln -s /usr/bin/aarch64-linux-gnu-g++-8 /usr/local/bin/aarch64-linux-gnu-g++ \
    && update-alternatives --set x86_64-w64-mingw32-gcc /usr/bin/x86_64-w64-mingw32-gcc-posix \
    && update-alternatives --set x86_64-w64-mingw32-g++ /usr/bin/x86_64-w64-mingw32-g++-posix \
    && rm -rf /var/lib/apt/lists/*
