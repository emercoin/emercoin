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
#   ci/build.sh package      # release build for $HOST, archived in dist/
#
# Environment: HOST (default x86_64-linux-gnu; also aarch64-linux-gnu, x86_64-w64-mingw32),
# JOBS (default: nproc), FUNC_JOBS (default: 2 x nproc, the tests mostly wait), TEST_TIMEOUT
# (seconds per functional test, default 600), TMPDIR_PREFIX (functional test data and logs,
# default /tmp/functional), DISTNAME (package name, default emercoin-<version>).
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
package)
    # The release build of contrib/gitian-descriptors (flags, security and symbol checks,
    # layout), headless for now: dist/$DISTNAME-$HOST.tar.gz, on Windows dist/$DISTNAME-win64.zip.
    # No libemercoinconsensus, as in the released packages: it does not link on its own yet
    # (consensus/tx_check.cpp uses randpaytx, defined in coins.cpp).
    case "$HOST" in
    *-mingw32) extra=(); ldflags=""; strip=(-s) ;;
    *)         extra=(--enable-glibc-back-compat); ldflags="-static-libstdc++"; strip=(--strip-debug) ;;
    esac
    ./autogen.sh
    CONFIG_SITE="$PWD/depends/$HOST/share/config.site" ./configure --prefix=/ \
        --disable-ccache --disable-maintainer-mode --without-gui --disable-bench --disable-gui-tests \
        --enable-reduce-exports --enable-util-tx --without-libs "${extra[@]}" \
        CFLAGS="-O2 -g" CXXFLAGS="-O2 -g" LDFLAGS="$ldflags"
    make -j"$JOBS"
    make -C src check-security
    [[ $HOST == *-mingw32 ]] || make -C src check-symbols

    distname="${DISTNAME:-emercoin-$(sed -n 's/^PACKAGE_VERSION = //p' Makefile)}"
    epoch="$(git log -1 --format=%ct)"
    rm -rf dist
    make install DESTDIR="$PWD/dist/install/$distname"
    cp doc/README.md "dist/install/$distname/"
    cd dist/install
    find . \( -name 'lib*.la' -o -name 'lib*.a' \) -delete
    rm -rf "$distname/lib/pkgconfig"
    if [[ $HOST == *-mingw32 ]]; then
        mv "$distname"/bin/*.dll "$distname/lib/" 2>/dev/null || true
    fi
    for dir in "$distname/bin" "$distname/lib"; do
        [ -d "$dir" ] && find "$dir" -type f -exec "$HOST-strip" "${strip[@]}" {} +
    done
    find "$distname" -exec touch -h -d "@$epoch" {} +
    if [[ $HOST == *-mingw32 ]]; then
        find "$distname" -type f | sort | zip -X -q -@ "../$distname-win64.zip"
    else
        find "$distname" | sort |
            tar --no-recursion --mode='u+rw,go+r-w,a+X' --owner=0 --group=0 -c -T - | gzip -9n > "../$distname-$HOST.tar.gz"
    fi
    cd ../..
    rm -rf dist/install
    ls -l dist
    ;;
*)
    echo "usage: $0 depends|build|check|functional|package" >&2
    exit 2
    ;;
esac
