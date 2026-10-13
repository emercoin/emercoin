#!/usr/bin/env bash
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Build and test stages, run from the source root inside the ci/Dockerfile image
# (ci/docker.sh does that):
#
#   ci/build.sh depends      # depends/ for $HOST, without Qt
#   ci/build.sh build        # configure + make: daemon, cli, tx, wallet tool, unit tests
#   ci/build.sh check        # unit tests (make check)
#   ci/build.sh functional   # functional tests (test/functional/test_runner.py)
#
# Environment: HOST (default x86_64-linux-gnu), JOBS (default: nproc), FUNC_JOBS (default:
# 2 x nproc, the tests mostly wait), TEST_TIMEOUT (seconds per functional test, default 600),
# TMPDIR_PREFIX (functional test data and logs, default /tmp/functional).
set -euo pipefail

HOST="${HOST:-x86_64-linux-gnu}"
JOBS="${JOBS:-$(nproc)}"

case "${1:-}" in
depends)
    make -C depends -j"$JOBS" HOST="$HOST" NO_QT=1
    ;;
build)
    ./autogen.sh
    CONFIG_SITE="$PWD/depends/$HOST/share/config.site" ./configure --prefix=/ \
        --without-gui --disable-bench --enable-tests --enable-util-tx \
        --enable-reduce-exports --disable-ccache --disable-maintainer-mode
    make -j"$JOBS"
    ;;
check)
    make -j"$JOBS" check
    ;;
functional)
    # One hung test would hold the whole run: stop any single test after TEST_TIMEOUT seconds.
    timeout="${TEST_TIMEOUT:-600}"
    ( while sleep 15; do
        ps -eo pid=,etimes=,args= |
        awk -v lim="$timeout" '$3 ~ /python3$/ && $4 ~ /test\/functional\/[a-z0-9_]+\.py$/ &&
                               $4 !~ /test_runner/ && $2 > lim {print $1, $4}' |
        while read -r pid script; do
            echo "WATCHDOG: stopped $script after more than $timeout s"
            kill "$pid"
        done
      done ) &
    watchdog=$!
    trap 'kill $watchdog' EXIT
    test/functional/test_runner.py -j"${FUNC_JOBS:-$(( $(nproc) * 2 ))}" --ci --combinedlogslen=200 \
        --tmpdirprefix="${TMPDIR_PREFIX:-/tmp/functional}"
    ;;
*)
    echo "usage: $0 depends|build|check|functional" >&2
    exit 2
    ;;
esac
