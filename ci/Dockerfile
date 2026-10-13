# CI and build image: Ubuntu 18.04 + gcc 8, the toolchain of the release builds
# (contrib/gitian-descriptors/gitian-linux.yml). Headless x86_64 for now.
FROM ubuntu:18.04

ENV DEBIAN_FRONTEND=noninteractive TZ=UTC LC_ALL=C.UTF-8 LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential gcc-8 g++-8 libtool autotools-dev automake autoconf \
        pkg-config bsdmainutils curl ca-certificates git python3 python3-zmq \
        patch xz-utils \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 80 \
                           --slave /usr/bin/g++ g++ /usr/bin/g++-8 \
    && rm -rf /var/lib/apt/lists/*
