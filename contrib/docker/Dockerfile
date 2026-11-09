# syntax=docker/dockerfile:1
#
# Emercoin Core node image (emercoind + emercoin-cli), published as emercoin/core and
# ghcr.io/emercoin/core by .github/workflows/docker.yml from the binaries of a published
# release. The build context has one directory per Docker architecture with the two
# binaries taken from that release's Linux tarball:
#
#   amd64/emercoind amd64/emercoin-cli     (emercoin-<version>-x86_64-linux-gnu.tar.gz)
#   arm64/emercoind arm64/emercoin-cli     (emercoin-<version>-aarch64-linux-gnu.tar.gz)
#
#   docker buildx build --platform linux/amd64,linux/arm64 -f contrib/docker/Dockerfile <context>
#
# Nothing runs inside the target image during the build, so arm64 builds on an amd64 host
# without emulation. The binaries need only glibc and libgcc_s, both in debian-slim.
#
# Data and emercoin.conf live in /srv/emercoind (a volume). Without a config file the node
# runs with the defaults; to use RPC from outside the container, mount a config, e.g.
#   -v ./emercoin.conf:/srv/emercoind/emercoin.conf:ro
# with rpcuser/rpcpassword (or rpcauth), rpcallowip and rpcbind.

FROM debian:trixie-slim
ARG TARGETARCH
ARG VERSION=unknown
LABEL org.opencontainers.image.title="Emercoin Core" \
      org.opencontainers.image.description="Emercoin node (emercoind) and emercoin-cli" \
      org.opencontainers.image.source="https://github.com/emercoin/emercoin" \
      org.opencontainers.image.url="https://emercoin.com" \
      org.opencontainers.image.licenses="MIT" \
      org.opencontainers.image.version="${VERSION}"
COPY ${TARGETARCH}/emercoind ${TARGETARCH}/emercoin-cli /bin/
WORKDIR /srv/emercoind
VOLUME /srv/emercoind
# P2P, RPC, EmerDNS
EXPOSE 6661 6662 5335/udp
CMD ["emercoind", "-datadir=/srv/emercoind", "-conf=/srv/emercoind/emercoin.conf", "-printtoconsole"]
