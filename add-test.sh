#!/usr/bin/env bash
for A in "$@"; do
    OBJDUMPFLAGS=$(grep 'OBJDUMP-FLAGS: ' "$A" | sed 's#^.*OBJDUMP-FLAGS: ##' | sed 's#}$##')
    if [[ -z "$OBJDUMPFLAGS" ]]; then
        OBJDUMPFLAGS="-s"
    fi
    ./compile-test.sh "$A" && mips-linux-gnu-objdump $OBJDUMPFLAGS "${A%.*}.o" > "${A%.*}.objdump"
done
