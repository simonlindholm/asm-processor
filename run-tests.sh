#!/usr/bin/env bash
for A in tests/*.c tests/*.p; do
    OBJDUMPFLAGS=$(grep 'OBJDUMP-FLAGS: ' "$A" | sed 's#^.*OBJDUMP-FLAGS: ##' | sed 's#}$##')
    if [[ -z "$OBJDUMPFLAGS" ]]; then
        OBJDUMPFLAGS="-s"
    fi
    echo $A
    ./compile-test.sh "$A" && mips-linux-gnu-objdump $OBJDUMPFLAGS "${A%.*}.o" | diff - "${A%.*}.objdump" || echo FAIL "$A"
done
