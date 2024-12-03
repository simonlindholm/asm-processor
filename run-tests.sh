#!/usr/bin/env bash
cd "$(dirname "${BASH_SOURCE[0]}")"
for A in tests/*.c tests/*.p; do
    OBJDUMPFLAGS=-srt
    echo $A
    ./compile-test.sh "$A" && mips-linux-gnu-objdump $OBJDUMPFLAGS "${A%.*}.o" | diff -w "${A%.*}.objdump" - || (echo FAIL "$A" && exit 1)
done
