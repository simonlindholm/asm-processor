// COMPILE-FLAGS: -O2
// ASMP-FLAGS: --asm-prelude $CWD/custom-prelude.s

GLOBAL_ASM(
glabel foo
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
endlabel foo
)
