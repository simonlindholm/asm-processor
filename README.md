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
lui	$at, %hi(rv)
jr	$ra
lwc1	$f0, %lo(rv)($at)
jr	$ra
nop
jr	$ra
nop
nop
)
```

To compile the file, run `./compile.sh file.c`, or invoke the `asm-processor.py` script in a similar manner. (`compile.sh` is mostly just intended to describe example usage.)
