#!/usr/bin/env bash
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Run a ci/build.sh stage in the CI image, on this source tree, as the calling user:
#
#   docker build -t emercoin-ci:bionic ci
#   ci/docker.sh depends && ci/docker.sh build && ci/docker.sh check && ci/docker.sh functional
#
# IMAGE selects another image tag. Functional tests run without network, so that a node
# started with a wrong configuration cannot reach mainnet peers.
set -euo pipefail

IMAGE="${IMAGE:-emercoin-ci:bionic}"
net=()
[ "${1:-}" = functional ] && net=(--network none)
exec docker run --rm "${net[@]}" --user "$(id -u):$(id -g)" -e HOME=/tmp -e USER=ci \
    -e HOST -e JOBS -e FUNC_JOBS -e TEST_TIMEOUT -e TMPDIR_PREFIX -e DISTNAME \
    -v "$PWD:/src" -w /src "$IMAGE" ci/build.sh "$@"
