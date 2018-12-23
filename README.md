# asm-processor

Pre-process .c files and post-process .o files to enable embedding MIPS assembly into IRIX-compiled C.

This can be useful for decompilation, as it allows:

 * postponing harder (e.g. `-O2`-compiled) functions
 * getting byte-exact matches for partially decompiled files
 * decompiling functions in the middle of files

## Usage

Let's say you have a file compiled with `-g` on the IRIX compiler, that looks like this:
```c
float func4(void) {
    "func4";
    return 0.2f;
}
```

This script enables replacing it by:
```asm
GLOBAL_ASM(
.rdata
.word 0x66756e63 # func
.word 0x34000000 # 4\0\0\0

.late_rodata
glabel rv
.word 0x3e4ccccd # 0.2f

.text
glabel func4
lui     $at, %hi(rv)
jr      $ra
lwc1    $f0, %lo(rv)($at)
jr      $ra
nop
jr      $ra
nop
)
```

To compile the file, run `./compile.sh file.c`, or invoke the `asm-processor.py` script in a similar manner. (`compile.sh` is mostly just intended to describe example usage.)

### What is supported?

`.text`, `.data`, `.bss` and `.rodata` sections, `.word`/`.incbin`, and `-g` and `-O2` flags to the IRIX compiler.

### What is not supported?

complicated assembly (.ifdef, macro declarations/calls other than `glabel`, pseudo-instructions that expand to several real instructions), too large `.late_rodata`/`.text` ratios within a block.

C `#ifdef`s only work outside of `GLOBAL_ASM` calls, but is otherwise able to replace `.ifdef`.

### What's up with "late rodata"?

The IRIX compiler emits rodata in two passes: first array/string contents, then large literals/switch jump tables.

Data declared within `.rdata`/`.section .rodata` will end up in the first half, and `.late_rodata`/`.section .late_rodata` in the second half.
