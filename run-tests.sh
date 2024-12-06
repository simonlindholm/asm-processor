#!/usr/bin/env bash

if [[ -z "$MIPS_CC" ]]; then
    echo "MIPS_CC not set"
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")"

OBJDUMPFLAGS=-srt
for typ in "python" "rust"; do
    for A in tests/*.c tests/*.p; do
        echo "$A ($typ)"
        ./compile-test.sh "$A" $typ && mips-linux-gnu-objdump $OBJDUMPFLAGS "${A%.*}.o" | diff -w "${A%.*}.objdump" - || (echo FAIL "$A" && exit 1)
    done
done