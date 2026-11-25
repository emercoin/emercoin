# CI and build image: Ubuntu 18.04 + gcc 8, the toolchain of the release builds
# (contrib/gitian-descriptors/gitian-linux.yml).
# Hosts: x86_64-linux-gnu (native), aarch64-linux-gnu. Windows: ci/Dockerfile.mingw.
FROM ubuntu:18.04

ENV DEBIAN_FRONTEND=noninteractive TZ=UTC LC_ALL=C.UTF-8 LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential gcc-8 g++-8 libtool autotools-dev automake autoconf \
        pkg-config bsdmainutils curl ca-certificates git python3 python3-zmq \
        patch xz-utils bison \
        g++-8-aarch64-linux-gnu gcc-8-aarch64-linux-gnu binutils-aarch64-linux-gnu \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 80 \
                           --slave /usr/bin/g++ g++ /usr/bin/g++-8 \
    && ln -s /usr/bin/aarch64-linux-gnu-gcc-8 /usr/local/bin/aarch64-linux-gnu-gcc \
    && ln -s /usr/bin/aarch64-linux-gnu-g++-8 /usr/local/bin/aarch64-linux-gnu-g++ \
    && rm -rf /var/lib/apt/lists/*
