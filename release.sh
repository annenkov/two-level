#!/bin/bash -e

function usage() {
    echo "Usage: $0 OUTPUT" >&2
    exit 2
}

function cleanup() {
    # [ -z "$tmp" ] || rm -fr "$tmp"
    echo "deleting"
}

out="$1"
[ -z "$out" ] && usage
out=$(readlink -f "$out")

trap cleanup EXIT
tmp=`mktemp -d`
mkdir -p "$tmp"
cd ..
git archive --format=tar HEAD | (cd "$tmp" && tar xf -)

cd "$tmp/lean"
bash fix-references.sh
cd ..
mv lean two-level-lean
zip -r "$out" two-level-lean
