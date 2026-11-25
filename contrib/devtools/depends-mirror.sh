#!/usr/bin/env bash
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Add the depends/ source archives that the Emercoin mirror lacks:
#
#   contrib/devtools/depends-mirror.sh [sources dir]   # default: depends/sources
#
# Downloads every source archive the Linux and Windows builds use into the sources dir (as
# depends/ does: mirror first, then upstream, each checked against the package's sha256),
# then uploads those missing from the mirror as assets of the `sources` release of
# emercoin/depends-sources (REPO overrides). Needs gh with write access to that repository.
# DRY_RUN=1 lists the missing files without uploading them.
set -euo pipefail

REPO="${REPO:-emercoin/depends-sources}"
TAG=sources
top="$(git rev-parse --show-toplevel)"
src="$(realpath -m "${1:-$top/depends/sources}")"
mkdir -p "$src"

hosts=(x86_64-unknown-linux-gnu x86_64-w64-mingw32)
needed=()
for host in "${hosts[@]}"; do
    make -s -C "$top/depends" HOST="$host" SOURCES_PATH="$src" download-one
    while read -r f; do needed+=("$f"); done < <(make -s -C "$top/depends" HOST="$host" print-sources)
done
mapfile -t needed < <(printf '%s\n' "${needed[@]}" | sort -u)

if ! gh release view "$TAG" --repo "$REPO" > /dev/null 2>&1; then
    if [ "${DRY_RUN:-0}" = 1 ]; then
        echo "release $TAG does not exist in $REPO yet"
    else
        gh release create "$TAG" --repo "$REPO" --title "depends sources" \
            --notes "Source archives for depends/ of Emercoin Core, under their depends/packages/*.mk file names."
    fi
fi
mapfile -t have < <(gh release view "$TAG" --repo "$REPO" --json assets --jq '.assets[].name' 2>/dev/null || true)

missing=()
for f in "${needed[@]}"; do
    printf '%s\n' "${have[@]}" | grep -qxF -- "$f" || missing+=("$src/$f")
done
if [ ${#missing[@]} = 0 ]; then
    echo "mirror has all ${#needed[@]} archives"
    exit 0
fi
printf 'missing: %s\n' "${missing[@]##*/}"

# download-one skips archives already in the sources dir without hashing them (depends/ checks
# the hash only when it extracts them), so check that each file to upload has a sha256 from one
# of the package recipes.
known="$(grep -ohE '\b[0-9a-f]{64}\b' "$top"/depends/packages/*.mk | sort -u)"
for f in "${missing[@]}"; do
    h="$(sha256sum "$f" | cut -d' ' -f1)"
    grep -qxF "$h" <<< "$known" || { echo "error: ${f##*/}: sha256 $h is not in depends/packages" >&2; exit 1; }
done
[ "${DRY_RUN:-0}" = 1 ] && exit 0
gh release upload "$TAG" --repo "$REPO" "${missing[@]}"
echo "uploaded ${#missing[@]} of ${#needed[@]} archives"
