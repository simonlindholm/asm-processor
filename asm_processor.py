#!/usr/bin/env python3
import argparse
from collections import namedtuple
from io import StringIO
import os
from pathlib import Path
import re
import struct
import sys
import tempfile

MAX_FN_SIZE = 100
SLOW_CHECKS = False

EI_NIDENT     = 16
EI_CLASS      = 4
EI_DATA       = 5
EI_VERSION    = 6
EI_OSABI      = 7
EI_ABIVERSION = 8
STN_UNDEF = 0

SHN_UNDEF     = 0
SHN_ABS       = 0xfff1
SHN_COMMON    = 0xfff2
SHN_XINDEX    = 0xffff
SHN_LORESERVE = 0xff00

STT_NOTYPE  = 0
STT_OBJECT  = 1
STT_FUNC    = 2
STT_SECTION = 3
STT_FILE    = 4
STT_COMMON  = 5
STT_TLS     = 6

STB_LOCAL  = 0
STB_GLOBAL = 1
STB_WEAK   = 2

STV_DEFAULT   = 0
STV_INTERNAL  = 1
STV_HIDDEN    = 2
STV_PROTECTED = 3

SHT_NULL          = 0
SHT_PROGBITS      = 1
SHT_SYMTAB        = 2
SHT_STRTAB        = 3
SHT_RELA          = 4
SHT_HASH          = 5
SHT_DYNAMIC       = 6
SHT_NOTE          = 7
SHT_NOBITS        = 8
SHT_REL           = 9
SHT_SHLIB         = 10
SHT_DYNSYM        = 11
SHT_INIT_ARRAY    = 14
SHT_FINI_ARRAY    = 15
SHT_PREINIT_ARRAY = 16
SHT_GROUP         = 17
SHT_SYMTAB_SHNDX  = 18
SHT_MIPS_GPTAB    = 0x70000003
SHT_MIPS_DEBUG    = 0x70000005
SHT_MIPS_REGINFO  = 0x70000006
SHT_MIPS_OPTIONS  = 0x7000000d

SHF_WRITE            = 0x1
SHF_ALLOC            = 0x2
SHF_EXECINSTR        = 0x4
SHF_MERGE            = 0x10
SHF_STRINGS          = 0x20
SHF_INFO_LINK        = 0x40
SHF_LINK_ORDER       = 0x80
SHF_OS_NONCONFORMING = 0x100
SHF_GROUP            = 0x200
SHF_TLS              = 0x400

R_MIPS_32   = 2
R_MIPS_26   = 4
R_MIPS_HI16 = 5
R_MIPS_LO16 = 6

MIPS_DEBUG_ST_STATIC = 2
MIPS_DEBUG_ST_PROC = 6
MIPS_DEBUG_ST_BLOCK = 7
MIPS_DEBUG_ST_END = 8
MIPS_DEBUG_ST_FILE = 11
MIPS_DEBUG_ST_STATIC_PROC = 14
MIPS_DEBUG_ST_STRUCT = 26
MIPS_DEBUG_ST_UNION = 27
MIPS_DEBUG_ST_ENUM = 28


class ElfFormat:
    def __init__(self, is_big_endian):
        self.is_big_endian = is_big_endian
        self.struct_char = ">" if is_big_endian else "<"

    def pack(self, fmt, *args):
        return struct.pack(self.struct_char + fmt, *args)

    def unpack(self, fmt, data):
        return struct.unpack(self.struct_char + fmt, data)


class Encoding:
    def __init__(self, encoding):
        self.encoding = encoding
        self.is_euc_jp = encoding.lower().replace("_", "").replace("-", "") == "eucjp"

    def encode(self, s):
        if self.is_euc_jp:
            s = s.replace("～", "〜")
        return s.encode(self.encoding)


class ElfHeader:
    """
    typedef struct {
        unsigned char   e_ident[EI_NIDENT];
        Elf32_Half      e_type;
        Elf32_Half      e_machine;
        Elf32_Word      e_version;
        Elf32_Addr      e_entry;
        Elf32_Off       e_phoff;
        Elf32_Off       e_shoff;
        Elf32_Word      e_flags;
        Elf32_Half      e_ehsize;
        Elf32_Half      e_phentsize;
        Elf32_Half      e_phnum;
        Elf32_Half      e_shentsize;
        Elf32_Half      e_shnum;
        Elf32_Half      e_shstrndx;
    } Elf32_Ehdr;
    """

    def __init__(self, data):
        self.e_ident = data[:EI_NIDENT]
        assert self.e_ident[EI_CLASS] == 1 # 32-bit
        self.fmt = ElfFormat(is_big_endian=(self.e_ident[EI_DATA] == 2))
        self.e_type, self.e_machine, self.e_version, self.e_entry, self.e_phoff, self.e_shoff, self.e_flags, self.e_ehsize, self.e_phentsize, self.e_phnum, self.e_shentsize, self.e_shnum, self.e_shstrndx = self.fmt.unpack('HHIIIIIHHHHHH', data[EI_NIDENT:])
        assert self.e_type == 1 # relocatable
        assert self.e_machine == 8 # MIPS I Architecture
        assert self.e_phoff == 0 # no program header
        assert self.e_shoff != 0 # section header
        assert self.e_shstrndx != SHN_UNDEF

    def to_bin(self):
        return self.e_ident + self.fmt.pack('HHIIIIIHHHHHH', self.e_type,
                self.e_machine, self.e_version, self.e_entry, self.e_phoff,
                self.e_shoff, self.e_flags, self.e_ehsize, self.e_phentsize,
                self.e_phnum, self.e_shentsize, self.e_shnum, self.e_shstrndx)


class Symbol:
    """
    typedef struct {
        Elf32_Word      st_name;
        Elf32_Addr      st_value;
        Elf32_Word      st_size;
        unsigned char   st_info;
        unsigned char   st_other;
        Elf32_Half      st_shndx;
    } Elf32_Sym;
    """

    def __init__(self, fmt, data, strtab, name=None):
        self.fmt = fmt
        self.st_name, self.st_value, self.st_size, st_info, self.st_other, self.st_shndx = fmt.unpack('IIIBBH', data)
        assert self.st_shndx != SHN_XINDEX, "too many sections (SHN_XINDEX not supported)"
        self.st_bind = st_info >> 4
        self.st_type = st_info & 0xf
        self.name = name if name is not None else strtab.lookup_str(self.st_name)
        self.st_visibility = self.st_other & 3

    @staticmethod
    def from_parts(fmt, st_name, st_value, st_size, st_info, st_other, st_shndx, strtab, name):
        header = fmt.pack('IIIBBH', st_name, st_value, st_size, st_info, st_other, st_shndx)
        return Symbol(fmt, header, strtab, name)

    def to_bin(self):
        st_info = (self.st_bind << 4) | self.st_type
        return self.fmt.pack('IIIBBH', self.st_name, self.st_value, self.st_size, st_info, self.st_other, self.st_shndx)


class Relocation:
    def __init__(self, fmt, data, sh_type):
        self.fmt = fmt
        self.sh_type = sh_type
        if sh_type == SHT_REL:
            self.r_offset, r_info = fmt.unpack('II', data)
        else:
            self.r_offset, r_info, self.r_addend = fmt.unpack('III', data)
        self.sym_index = r_info >> 8
        self.rel_type = r_info & 0xff

    def to_bin(self):
        r_info = (self.sym_index << 8) | self.rel_type
        if self.sh_type == SHT_REL:
            return self.fmt.pack('II', self.r_offset, r_info)
        else:
            return self.fmt.pack('III', self.r_offset, r_info, self.r_addend)


class Section:
    """
    typedef struct {
        Elf32_Word   sh_name;
        Elf32_Word   sh_type;
        Elf32_Word   sh_flags;
        Elf32_Addr   sh_addr;
        Elf32_Off    sh_offset;
        Elf32_Word   sh_size;
        Elf32_Word   sh_link;
        Elf32_Word   sh_info;
        Elf32_Word   sh_addralign;
        Elf32_Word   sh_entsize;
    } Elf32_Shdr;
    """

    def __init__(self, fmt, header, data, index):
        self.fmt = fmt
        self.sh_name, self.sh_type, self.sh_flags, self.sh_addr, self.sh_offset, self.sh_size, self.sh_link, self.sh_info, self.sh_addralign, self.sh_entsize = fmt.unpack('IIIIIIIIII', header)
        assert not self.sh_flags & SHF_LINK_ORDER
        if self.sh_entsize != 0:
            assert self.sh_size % self.sh_entsize == 0
        if self.sh_type == SHT_NOBITS:
            self.data = b''
        else:
            self.data = data[self.sh_offset:self.sh_offset + self.sh_size]
        self.index = index
        self.relocated_by = []

    @staticmethod
    def from_parts(fmt, sh_name, sh_type, sh_flags, sh_link, sh_info, sh_addralign, sh_entsize, data, index):
        header = fmt.pack('IIIIIIIIII', sh_name, sh_type, sh_flags, 0, 0, len(data), sh_link, sh_info, sh_addralign, sh_entsize)
        return Section(fmt, header, data, index)

    def lookup_str(self, index):
        assert self.sh_type == SHT_STRTAB
        to = self.data.find(b'\0', index)
        assert to != -1
        return self.data[index:to].decode('latin1')

    def add_str(self, string):
        assert self.sh_type == SHT_STRTAB
        ret = len(self.data)
        self.data += string.encode('latin1') + b'\0'
        return ret

    def is_rel(self):
        return self.sh_type == SHT_REL or self.sh_type == SHT_RELA

    def header_to_bin(self):
        if self.sh_type != SHT_NOBITS:
            self.sh_size = len(self.data)
        return self.fmt.pack('IIIIIIIIII', self.sh_name, self.sh_type, self.sh_flags, self.sh_addr, self.sh_offset, self.sh_size, self.sh_link, self.sh_info, self.sh_addralign, self.sh_entsize)

    def init_relocs(self):
        assert self.is_rel()
        entries = []
        for i in range(0, self.sh_size, self.sh_entsize):
            entries.append(Relocation(self.fmt, self.data[i:i+self.sh_entsize], self.sh_type))
        self.relocations = entries

    def relocate_mdebug(self, original_offset):
        assert self.sh_type == SHT_MIPS_DEBUG
        new_data = bytearray(self.data)
        shift_by = self.sh_offset - original_offset

        # Update the file-relative offsets in the Symbolic HDRR
        hdrr_magic, hdrr_vstamp, hdrr_ilineMax, hdrr_cbLine, \
            hdrr_cbLineOffset, hdrr_idnMax, hdrr_cbDnOffset, hdrr_ipdMax, \
            hdrr_cbPdOffset, hdrr_isymMax, hdrr_cbSymOffset, hdrr_ioptMax, \
            hdrr_cbOptOffset, hdrr_iauxMax, hdrr_cbAuxOffset, hdrr_issMax, \
            hdrr_cbSsOffset, hdrr_issExtMax, hdrr_cbSsExtOffset, hdrr_ifdMax, \
            hdrr_cbFdOffset, hdrr_crfd, hdrr_cbRfdOffset, hdrr_iextMax, \
            hdrr_cbExtOffset = self.fmt.unpack("HHIIIIIIIIIIIIIIIIIIIIIII", self.data[0:0x60])

        assert hdrr_magic == 0x7009, "Invalid magic value for .mdebug symbolic header"

        if hdrr_cbLine: hdrr_cbLineOffset += shift_by
        if hdrr_idnMax: hdrr_cbDnOffset += shift_by
        if hdrr_ipdMax: hdrr_cbPdOffset += shift_by
        if hdrr_isymMax: hdrr_cbSymOffset += shift_by
        if hdrr_ioptMax: hdrr_cbOptOffset += shift_by
        if hdrr_iauxMax: hdrr_cbAuxOffset += shift_by
        if hdrr_issMax: hdrr_cbSsOffset += shift_by
        if hdrr_issExtMax: hdrr_cbSsExtOffset += shift_by
        if hdrr_ifdMax: hdrr_cbFdOffset += shift_by
        if hdrr_crfd: hdrr_cbRfdOffset += shift_by
        if hdrr_iextMax: hdrr_cbExtOffset += shift_by

        new_data[0:0x60] = self.fmt.pack("HHIIIIIIIIIIIIIIIIIIIIIII", hdrr_magic, hdrr_vstamp, hdrr_ilineMax, hdrr_cbLine, \
            hdrr_cbLineOffset, hdrr_idnMax, hdrr_cbDnOffset, hdrr_ipdMax, \
            hdrr_cbPdOffset, hdrr_isymMax, hdrr_cbSymOffset, hdrr_ioptMax, \
            hdrr_cbOptOffset, hdrr_iauxMax, hdrr_cbAuxOffset, hdrr_issMax, \
            hdrr_cbSsOffset, hdrr_issExtMax, hdrr_cbSsExtOffset, hdrr_ifdMax, \
            hdrr_cbFdOffset, hdrr_crfd, hdrr_cbRfdOffset, hdrr_iextMax, \
            hdrr_cbExtOffset)

        self.data = bytes(new_data)

class ElfFile:
    def __init__(self, data):
        self.data = data
        assert data[:4] == b'\x7fELF', "not an ELF file"

        self.elf_header = ElfHeader(data[0:52])
        self.fmt = self.elf_header.fmt

        offset, size = self.elf_header.e_shoff, self.elf_header.e_shentsize
        null_section = Section(self.fmt, data[offset:offset + size], data, 0)
        num_sections = self.elf_header.e_shnum or null_section.sh_size

        self.sections = [null_section]
        for i in range(1, num_sections):
            ind = offset + i * size
            self.sections.append(Section(self.fmt, data[ind:ind + size], data, i))

        symtab = None
        for s in self.sections:
            if s.sh_type == SHT_SYMTAB:
                assert not symtab
                symtab = s
        assert symtab is not None
        self.symtab = symtab
        self.sym_strtab = self.sections[symtab.sh_link]
        self.symbol_entries = ElfFile.init_symbols(symtab, self.sym_strtab)

        shstr = self.sections[self.elf_header.e_shstrndx]
        for s in self.sections:
            s.name = shstr.lookup_str(s.sh_name)
            if s.is_rel():
                self.sections[s.sh_info].relocated_by.append(s)
                s.init_relocs()

    @staticmethod
    def init_symbols(symtab, strtab):
        assert symtab.sh_type == SHT_SYMTAB
        assert symtab.sh_entsize == 16
        syms = []
        for i in range(0, symtab.sh_size, symtab.sh_entsize):
            syms.append(Symbol(symtab.fmt, symtab.data[i:i+symtab.sh_entsize], strtab))
        return syms

    def find_symbol(self, name):
        for s in self.symbol_entries:
            if s.name == name:
                return (s.st_shndx, s.st_value)
        return None

    def find_symbol_in_section(self, name, section):
        pos = self.find_symbol(name)
        assert pos is not None
        assert pos[0] == section.index
        return pos[1]

    def find_section(self, name):
        for s in self.sections:
            if s.name == name:
                return s
        return None

    def add_section(self, name, sh_type, sh_flags, sh_link, sh_info, sh_addralign, sh_entsize, data):
        shstr = self.sections[self.elf_header.e_shstrndx]
        sh_name = shstr.add_str(name)
        s = Section.from_parts(self.fmt, sh_name=sh_name, sh_type=sh_type,
                sh_flags=sh_flags, sh_link=sh_link, sh_info=sh_info,
                sh_addralign=sh_addralign, sh_entsize=sh_entsize, data=data,
                index=len(self.sections))
        self.sections.append(s)
        s.name = name
        return s

    def drop_mdebug_gptab(self):
        # We can only drop sections at the end, since otherwise section
        # references might be wrong. Luckily, these sections typically are.
        while self.sections[-1].sh_type in [SHT_MIPS_DEBUG, SHT_MIPS_GPTAB]:
            self.sections.pop()

    def write(self, filename):
        outfile = open(filename, 'wb')
        outidx = 0
        def write_out(data):
            nonlocal outidx
            outfile.write(data)
            outidx += len(data)
        def pad_out(align):
            if align and outidx % align:
                write_out(b'\0' * (align - outidx % align))

        self.elf_header.e_shnum = len(self.sections)
        write_out(self.elf_header.to_bin())

        for s in self.sections:
            if s.sh_type != SHT_NOBITS and s.sh_type != SHT_NULL:
                pad_out(s.sh_addralign)
                old_offset = s.sh_offset
                s.sh_offset = outidx
                if s.sh_type == SHT_MIPS_DEBUG and s.sh_offset != old_offset:
                    # The .mdebug section has moved, relocate offsets
                    s.relocate_mdebug(old_offset)
                write_out(s.data)

        pad_out(4)
        self.elf_header.e_shoff = outidx
        for s in self.sections:
            write_out(s.header_to_bin())

        outfile.seek(0)
        outfile.write(self.elf_header.to_bin())
        outfile.close()


def is_temp_name(name):
    return name.startswith('_asmpp_')


# https://stackoverflow.com/a/241506
def re_comment_replacer(match):
    s = match.group(0)
    if s[0] in "/#":
        return " "
    else:
        return s


re_comment_or_string = re.compile(
    r'#.*|/\*.*?\*/|"(?:\\.|[^\\"])*"'
)


class Failure(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


class GlobalState:
    def __init__(self, min_instr_count, skip_instr_count, use_jtbl_for_rodata, prelude_if_late_rodata, mips1, pascal):
        # A value that hopefully never appears as a 32-bit rodata constant (or we
        # miscompile late rodata). Increases by 1 in each step.
        self.late_rodata_hex = 0xE0123456
        self.valuectr = 0
        self.namectr = 0
        self.min_instr_count = min_instr_count
        self.skip_instr_count = skip_instr_count
        self.use_jtbl_for_rodata = use_jtbl_for_rodata
        self.prelude_if_late_rodata = prelude_if_late_rodata
        self.mips1 = mips1
        self.pascal = pascal

    def next_late_rodata_hex(self):
        dummy_bytes = struct.pack('>I', self.late_rodata_hex)
        if (self.late_rodata_hex & 0xffff) == 0:
            # Avoid lui
            self.late_rodata_hex += 1
        self.late_rodata_hex += 1
        return dummy_bytes

    def make_name(self, cat):
        self.namectr += 1
        return '_asmpp_{}{}'.format(cat, self.namectr)

    def func_prologue(self, name):
        if self.pascal:
            return " ".join([
                "procedure {}();".format(name),
                "type",
                " pi = ^integer;",
                " pf = ^single;",
                " pd = ^double;",
                "var",
                " vi: pi;",
                " vf: pf;",
                " vd: pd;",
                "begin",
                " vi := vi;",
                " vf := vf;",
                " vd := vd;",
            ])
        else:
            return 'void {}(void) {{'.format(name)

    def func_epilogue(self):
        if self.pascal:
            return "end;"
        else:
            return "}"

    def pascal_assignment(self, tp, val):
        self.valuectr += 1
        address = (8 * self.valuectr) & 0x7FFF
        return 'v{} := p{}({}); v{}^ := {};'.format(tp, tp, address, tp, val)

Function = namedtuple('Function', ['text_glabels', 'asm_conts', 'late_rodata_dummy_bytes', 'jtbl_rodata_size', 'late_rodata_asm_conts', 'fn_desc', 'data'])


class GlobalAsmBlock:
    def __init__(self, fn_desc):
        self.fn_desc = fn_desc
        self.cur_section = '.text'
        self.asm_conts = []
        self.late_rodata_asm_conts = []
        self.late_rodata_alignment = 0
        self.late_rodata_alignment_from_content = False
        self.text_glabels = []
        self.fn_section_sizes = {
            '.text': 0,
            '.data': 0,
            '.bss': 0,
            '.rodata': 0,
            '.late_rodata': 0,
        }
        self.fn_ins_inds = []
        self.glued_line = ''
        self.num_lines = 0

    def fail(self, message, line=None):
        context = self.fn_desc
        if line:
            context += ", at line \"" + line + "\""
        raise Failure(message + "\nwithin " + context)

    def count_quoted_size(self, line, z, real_line, output_enc):
        line = output_enc.encode(line).decode('latin1')
        in_quote = False
        has_comma = True
        num_parts = 0
        ret = 0
        i = 0
        digits = "0123456789" # 0-7 would be more sane, but this matches GNU as
        while i < len(line):
            c = line[i]
            i += 1
            if not in_quote:
                if c == '"':
                    in_quote = True
                    if z and not has_comma:
                        self.fail(".asciiz with glued strings is not supported due to GNU as version diffs")
                    num_parts += 1
                elif c == ',':
                    has_comma = True
            else:
                if c == '"':
                    in_quote = False
                    has_comma = False
                    continue
                ret += 1
                if c != '\\':
                    continue
                if i == len(line):
                    self.fail("backslash at end of line not supported", real_line)
                c = line[i]
                i += 1
                # (if c is in "bfnrtv", we have a real escaped literal)
                if c == 'x':
                    # hex literal, consume any number of hex chars, possibly none
                    while i < len(line) and line[i] in digits + "abcdefABCDEF":
                        i += 1
                elif c in digits:
                    # octal literal, consume up to two more digits
                    it = 0
                    while i < len(line) and line[i] in digits and it < 2:
                        i += 1
                        it += 1

        if in_quote:
            self.fail("unterminated string literal", real_line)
        if num_parts == 0:
            self.fail(".ascii with no string", real_line)
        return ret + num_parts if z else ret

    def align2(self):
        while self.fn_section_sizes[self.cur_section] % 2 != 0:
            self.fn_section_sizes[self.cur_section] += 1

    def align4(self):
        while self.fn_section_sizes[self.cur_section] % 4 != 0:
            self.fn_section_sizes[self.cur_section] += 1

    def add_sized(self, size, line):
        if self.cur_section in ['.text', '.late_rodata']:
            if size % 4 != 0:
                self.fail("size must be a multiple of 4", line)
        if size < 0:
            self.fail("size cannot be negative", line)
        self.fn_section_sizes[self.cur_section] += size
        if self.cur_section == '.text':
            if not self.text_glabels:
                self.fail(".text block without an initial glabel", line)
            self.fn_ins_inds.append((self.num_lines - 1, size // 4))

    def process_line(self, line, output_enc):
        self.num_lines += 1
        if line.endswith('\\'):
            self.glued_line += line[:-1]
            return
        line = self.glued_line + line
        self.glued_line = ''

        real_line = line
        line = re.sub(re_comment_or_string, re_comment_replacer, line)
        line = line.strip()
        line = re.sub(r'^[a-zA-Z0-9_]+:\s*', '', line)
        changed_section = False
        emitting_double = False
        if (line.startswith('glabel ') or line.startswith('jlabel ')) and self.cur_section == '.text':
            self.text_glabels.append(line.split()[1])
        if not line:
            pass # empty line
        elif line.startswith('glabel ') or line.startswith('dlabel ') or line.startswith('jlabel ') or line.startswith('endlabel ') or (' ' not in line and line.endswith(':')):
            pass # label
        elif line.startswith('.section') or line in ['.text', '.data', '.rdata', '.rodata', '.bss', '.late_rodata']:
            # section change
            self.cur_section = '.rodata' if line == '.rdata' else line.split(',')[0].split()[-1]
            if self.cur_section not in ['.data', '.text', '.rodata', '.late_rodata', '.bss']:
                self.fail("unrecognized .section directive", real_line)
            changed_section = True
        elif line.startswith('.late_rodata_alignment'):
            if self.cur_section != '.late_rodata':
                self.fail(".late_rodata_alignment must occur within .late_rodata section", real_line)
            value = int(line.split()[1])
            if value not in [4, 8]:
                self.fail(".late_rodata_alignment argument must be 4 or 8", real_line)
            if self.late_rodata_alignment and self.late_rodata_alignment != value:
                self.fail(".late_rodata_alignment alignment assumption conflicts with earlier .double directive. Make sure to provide explicit alignment padding.")
            self.late_rodata_alignment = value
            changed_section = True
        elif line.startswith('.incbin'):
            self.add_sized(int(line.split(',')[-1].strip(), 0), real_line)
        elif line.startswith('.word') or line.startswith('.gpword') or line.startswith('.float'):
            self.align4()
            self.add_sized(4 * len(line.split(',')), real_line)
        elif line.startswith('.double'):
            self.align4()
            if self.cur_section == '.late_rodata':
                align8 = self.fn_section_sizes[self.cur_section] % 8
                # Automatically set late_rodata_alignment, so the generated C code uses doubles.
                # This gives us correct alignment for the transferred doubles even when the
                # late_rodata_alignment is wrong, e.g. for non-matching compilation.
                if not self.late_rodata_alignment:
                    self.late_rodata_alignment = 8 - align8
                    self.late_rodata_alignment_from_content = True
                elif self.late_rodata_alignment != 8 - align8:
                    if self.late_rodata_alignment_from_content:
                        self.fail("found two .double directives with different start addresses mod 8. Make sure to provide explicit alignment padding.", real_line)
                    else:
                        self.fail(".double at address that is not 0 mod 8 (based on .late_rodata_alignment assumption). Make sure to provide explicit alignment padding.", real_line)
            self.add_sized(8 * len(line.split(',')), real_line)
            emitting_double = True
        elif line.startswith('.space'):
            self.add_sized(int(line.split()[1], 0), real_line)
        elif line.startswith('.balign'):
            align = int(line.split()[1])
            if align != 4:
                self.fail("only .balign 4 is supported", real_line)
            self.align4()
        elif line.startswith('.align'):
            align = int(line.split()[1])
            if align != 2:
                self.fail("only .align 2 is supported", real_line)
            self.align4()
        elif line.startswith('.asci'):
            z = (line.startswith('.asciz') or line.startswith('.asciiz'))
            self.add_sized(self.count_quoted_size(line, z, real_line, output_enc), real_line)
        elif line.startswith('.byte'):
            self.add_sized(len(line.split(',')), real_line)
        elif line.startswith('.half') or line.startswith('.hword') or line.startswith(".short"):
            self.align2()
            self.add_sized(2*len(line.split(',')), real_line)
        elif line.startswith('.size'):
            pass
        elif line.startswith('.'):
            # .macro, ...
            self.fail("asm directive not supported", real_line)
        else:
            # Unfortunately, macros are hard to support for .rodata --
            # we don't know how how space they will expand to before
            # running the assembler, but we need that information to
            # construct the C code. So if we need that we'll either
            # need to run the assembler twice (at least in some rare
            # cases), or change how this program is invoked.
            # Similarly, we can't currently deal with pseudo-instructions
            # that expand to several real instructions.
            if self.cur_section != '.text':
                self.fail("instruction or macro call in non-.text section? not supported", real_line)
            self.add_sized(4, real_line)
        if self.cur_section == '.late_rodata':
            if not changed_section:
                if emitting_double:
                    self.late_rodata_asm_conts.append(".align 0")
                self.late_rodata_asm_conts.append(real_line)
                if emitting_double:
                    self.late_rodata_asm_conts.append(".align 2")
        else:
            self.asm_conts.append(real_line)

    def finish(self, state):
        src = [''] * (self.num_lines + 1)
        late_rodata_dummy_bytes = []
        jtbl_rodata_size = 0
        late_rodata_fn_output = []

        num_instr = self.fn_section_sizes['.text'] // 4

        if self.fn_section_sizes['.late_rodata'] > 0:
            # Generate late rodata by emitting unique float constants.
            # This requires 3 instructions for each 4 bytes of rodata.
            # If we know alignment, we can use doubles, which give 3
            # instructions for 8 bytes of rodata.
            size = self.fn_section_sizes['.late_rodata'] // 4
            skip_next = False
            needs_double = (self.late_rodata_alignment != 0)
            extra_mips1_nop = False
            if state.pascal:
                jtbl_size = 9 if state.mips1 else 8
                jtbl_min_rodata_size = 2
            else:
                jtbl_size = 11 if state.mips1 else 9
                jtbl_min_rodata_size = 5
            for i in range(size):
                if skip_next:
                    skip_next = False
                    continue
                # Jump tables give 9 instructions (11 with -mips1) for >= 5 words of rodata,
                # and should be emitted when:
                # - -O2 or -O2 -g3 are used, which give the right codegen
                # - we have emitted our first .float/.double (to ensure that we find the
                #   created rodata in the binary)
                # - we have emitted our first .double, if any (to ensure alignment of doubles
                #   in shifted rodata sections)
                # - we have at least 5 words of rodata left to emit (otherwise IDO does not
                #   generate a jump table)
                # - we have at least 10 more instructions to go in this function (otherwise our
                #   function size computation will be wrong since the delay slot goes unused)
                if (not needs_double and state.use_jtbl_for_rodata and i >= 1 and
                        size - i >= jtbl_min_rodata_size and
                        num_instr - len(late_rodata_fn_output) >= jtbl_size + 1):
                    if state.pascal:
                        cases = "\n".join("{}: ;".format(case) for case in range(size - i))
                        line = "case 0 of " + cases + " otherwise end;"
                    else:
                        cases = " ".join("case {}:".format(case) for case in range(size - i))
                        line = "switch (*(volatile int*)0) { " + cases + " ; }"
                    late_rodata_fn_output.append(line)
                    late_rodata_fn_output.extend([""] * (jtbl_size - 1))
                    jtbl_rodata_size = (size - i) * 4
                    extra_mips1_nop = i != 2
                    break
                dummy_bytes = state.next_late_rodata_hex()
                late_rodata_dummy_bytes.append(dummy_bytes)
                if self.late_rodata_alignment == 4 * ((i + 1) % 2 + 1) and i + 1 < size:
                    dummy_bytes2 = state.next_late_rodata_hex()
                    late_rodata_dummy_bytes.append(dummy_bytes2)
                    fval, = struct.unpack('>d', dummy_bytes + dummy_bytes2)
                    if state.pascal:
                        line = state.pascal_assignment('d', fval)
                    else:
                        line = '*(volatile double*)0 = {};'.format(fval)
                    late_rodata_fn_output.append(line)
                    skip_next = True
                    needs_double = False
                    if state.mips1:
                        # mips1 does not have ldc1/sdc1
                        late_rodata_fn_output.append('')
                        late_rodata_fn_output.append('')
                    extra_mips1_nop = False
                else:
                    fval, = struct.unpack('>f', dummy_bytes)
                    if state.pascal:
                        line = state.pascal_assignment('f', fval)
                    else:
                        line = '*(volatile float*)0 = {}f;'.format(fval)
                    late_rodata_fn_output.append(line)
                    extra_mips1_nop = True
                late_rodata_fn_output.append('')
                late_rodata_fn_output.append('')
            if state.mips1 and extra_mips1_nop:
                late_rodata_fn_output.append('')

        text_name = None
        if self.fn_section_sizes['.text'] > 0 or late_rodata_fn_output:
            text_name = state.make_name('func')
            src[0] = state.func_prologue(text_name)
            src[self.num_lines] = state.func_epilogue()
            instr_count = self.fn_section_sizes['.text'] // 4
            if instr_count < state.min_instr_count:
                self.fail("too short .text block")
            tot_emitted = 0
            tot_skipped = 0
            fn_emitted = 0
            fn_skipped = 0
            skipping = True
            rodata_stack = late_rodata_fn_output[::-1]
            for (line, count) in self.fn_ins_inds:
                for _ in range(count):
                    if (fn_emitted > MAX_FN_SIZE and instr_count - tot_emitted > state.min_instr_count and
                            (not rodata_stack or rodata_stack[-1])):
                        # Don't let functions become too large. When a function reaches 284
                        # instructions, and -O2 -framepointer flags are passed, the IRIX
                        # compiler decides it is a great idea to start optimizing more.
                        # Also, Pascal cannot handle too large functions before it runs out
                        # of unique statements to write.
                        fn_emitted = 0
                        fn_skipped = 0
                        skipping = True
                        src[line] += (' ' + state.func_epilogue() + ' ' +
                            state.func_prologue(state.make_name('large_func')) + ' ')
                    if (
                        skipping and
                        fn_skipped < state.skip_instr_count +
                            (state.prelude_if_late_rodata if rodata_stack else 0)
                    ):
                        fn_skipped += 1
                        tot_skipped += 1
                    else:
                        skipping = False
                        if rodata_stack:
                            src[line] += rodata_stack.pop()
                        elif state.pascal:
                            src[line] += state.pascal_assignment('i', '0')
                        else:
                            src[line] += '*(volatile int*)0 = 0;'
                    tot_emitted += 1
                    fn_emitted += 1
            if rodata_stack:
                size = len(late_rodata_fn_output) // 3
                available = instr_count - tot_skipped
                self.fail(
                    "late rodata to text ratio is too high: {} / {} must be <= 1/3\n"
                    "add .late_rodata_alignment (4|8) to the .late_rodata "
                    "block to double the allowed ratio."
                        .format(size, available))

        rodata_name = None
        if self.fn_section_sizes['.rodata'] > 0:
            if state.pascal:
                self.fail(".rodata isn't supported with Pascal for now")
            rodata_name = state.make_name('rodata')
            src[self.num_lines] += ' const char {}[{}] = {{1}};'.format(rodata_name, self.fn_section_sizes['.rodata'])

        data_name = None
        if self.fn_section_sizes['.data'] > 0:
            data_name = state.make_name('data')
            if state.pascal:
                line = ' var {}: packed array[1..{}] of char := [otherwise: 0];'.format(data_name, self.fn_section_sizes['.data'])
            else:
                line = ' char {}[{}] = {{1}};'.format(data_name, self.fn_section_sizes['.data'])
            src[self.num_lines] += line

        bss_name = None
        if self.fn_section_sizes['.bss'] > 0:
            if state.pascal:
                self.fail(".bss isn't supported with Pascal")
            bss_name = state.make_name('bss')
            src[self.num_lines] += ' char {}[{}];'.format(bss_name, self.fn_section_sizes['.bss'])

        fn = Function(
                text_glabels=self.text_glabels,
                asm_conts=self.asm_conts,
                late_rodata_dummy_bytes=late_rodata_dummy_bytes,
                jtbl_rodata_size=jtbl_rodata_size,
                late_rodata_asm_conts=self.late_rodata_asm_conts,
                fn_desc=self.fn_desc,
                data={
                    '.text': (text_name, self.fn_section_sizes['.text']),
                    '.data': (data_name, self.fn_section_sizes['.data']),
                    '.rodata': (rodata_name, self.fn_section_sizes['.rodata']),
                    '.bss': (bss_name, self.fn_section_sizes['.bss']),
                })
        return src, fn

cutscene_data_regexpr = re.compile(r"CutsceneData (.|\n)*\[\] = {")
float_regexpr = re.compile(r"[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?f")

def repl_float_hex(m):
    return str(struct.unpack(">I", struct.pack(">f", float(m.group(0).strip().rstrip("f"))))[0])

Opts = namedtuple('Opts', ['opt', 'framepointer', 'mips1', 'kpic', 'pascal', 'input_enc', 'output_enc', 'encode_cutscene_data_floats'])

def parse_source(f, opts, out_dependencies, print_source=None):
    if opts.opt in ['O1', 'O2']:
        if opts.framepointer:
            min_instr_count = 6
            skip_instr_count = 5
        else:
            min_instr_count = 2
            skip_instr_count = 1
    elif opts.opt == 'O0':
        if opts.framepointer:
            min_instr_count = 8
            skip_instr_count = 8
        else:
            min_instr_count = 4
            skip_instr_count = 4
    elif opts.opt == 'g':
        if opts.framepointer:
            min_instr_count = 7
            skip_instr_count = 7
        else:
            min_instr_count = 4
            skip_instr_count = 4
    elif opts.opt == 'g3':
        if opts.framepointer:
            min_instr_count = 4
            skip_instr_count = 4
        else:
            min_instr_count = 2
            skip_instr_count = 2
    else:
        raise Failure("must pass one of -g, -O0, -O1, -O2, -O2 -g3")
    prelude_if_late_rodata = 0
    if opts.kpic:
        # Without optimizations, the PIC prelude always takes up 3 instructions.
        # With optimizations, the prelude is optimized out if there's no late rodata.
        if opts.opt in ('g3', 'O2'):
            prelude_if_late_rodata = 3
        else:
            min_instr_count += 3
            skip_instr_count += 3

    use_jtbl_for_rodata = False
    if opts.opt in ['O2', 'g3'] and not opts.framepointer and not opts.kpic:
        use_jtbl_for_rodata = True

    state = GlobalState(min_instr_count, skip_instr_count, use_jtbl_for_rodata, prelude_if_late_rodata, opts.mips1, opts.pascal)
    output_enc = opts.output_enc

    global_asm = None
    asm_functions = []
    base_fname = f.name
    output_lines = [
        '#line 1 "' + base_fname + '"'
    ]

    is_cutscene_data = False
    is_early_include = False

    for line_no, raw_line in enumerate(f, 1):
        raw_line = raw_line.rstrip()
        line = raw_line.lstrip()

        # Print exactly one output line per source line, to make compiler
        # errors have correct line numbers. These will be overridden with
        # reasonable content further down.
        output_lines.append('')

        if global_asm is not None:
            if line.startswith(')'):
                src, fn = global_asm.finish(state)
                if state.pascal:
                    # Pascal has a 1600-character line length limit, so some
                    # of the lines we emit may be broken up. Correct for that
                    # using a #line directive.
                    src[-1] += '\n#line ' + str(line_no + 1)
                for i, line2 in enumerate(src):
                    output_lines[start_index + i] = line2
                asm_functions.append(fn)
                global_asm = None
            else:
                global_asm.process_line(raw_line, output_enc)
        elif line in ("GLOBAL_ASM(", "#pragma GLOBAL_ASM("):
            global_asm = GlobalAsmBlock("GLOBAL_ASM block at line " + str(line_no))
            start_index = len(output_lines)
        elif (
            (line.startswith('GLOBAL_ASM("') or line.startswith('#pragma GLOBAL_ASM("'))
            and line.endswith('")')
        ) or (
            (line.startswith('INCLUDE_ASM("') or line.startswith('INCLUDE_RODATA("'))
            and '",' in line
            and line.endswith(");")
        ):
            prologue = []
            if line.startswith("INCLUDE_"):
                # INCLUDE_ASM("path/to", functionname);
                before, after = line.split('",', 1)
                fname = before[before.index("(") + 2 :] + "/" + after.strip()[:-2] + ".s"
                if line.startswith("INCLUDE_RODATA"):
                    prologue = [".section .rodata"]
            else:
                # GLOBAL_ASM("path/to/file.s")
                fname = line[line.index("(") + 2 : -2]
            ext_global_asm = GlobalAsmBlock(fname)
            for line2 in prologue:
                ext_global_asm.process_line(line2, output_enc)
            try:
                f = open(fname, encoding=opts.input_enc)
            except FileNotFoundError:
                # The GLOBAL_ASM block might be surrounded by an ifdef, so it's
                # not clear whether a missing file actually represents a compile
                # error. Pass the responsibility for determining that on to the
                # compiler by emitting a bad include directive. (IDO treats
                # #error as a warning for some reason.)
                output_lines[-1] = '#include "GLOBAL_ASM:' + fname + '"'
                continue
            with f:
                for line2 in f:
                    ext_global_asm.process_line(line2.rstrip(), output_enc)
            src, fn = ext_global_asm.finish(state)
            if state.pascal:
                # Pascal has a 1600-character line length limit, so avoid putting
                # everything on the same line.
                src.append('#line ' + str(line_no + 1))
                output_lines[-1] = '\n'.join(src)
            else:
                output_lines[-1] = ''.join(src)
            asm_functions.append(fn)
            out_dependencies.append(fname)
        elif line == '#pragma asmproc recurse':
            # C includes qualified as
            # #pragma asmproc recurse
            # #include "file.c"
            # will be processed recursively when encountered
            is_early_include = True
        elif is_early_include:
            # Previous line was a #pragma asmproc recurse
            is_early_include = False
            if not line.startswith("#include "):
                raise Failure("#pragma asmproc recurse must be followed by an #include")
            fpath = os.path.dirname(base_fname)
            fname = os.path.join(fpath, line[line.index(' ') + 2 : -1])
            out_dependencies.append(fname)
            include_src = StringIO()
            with open(fname, encoding=opts.input_enc) as include_file:
                parse_source(include_file, opts, out_dependencies, include_src)
            include_src.write('#line ' + str(line_no + 1) + ' "' + base_fname + '"')
            output_lines[-1] = include_src.getvalue()
            include_src.close()
        else:
            if opts.encode_cutscene_data_floats:
                # This is a hack to replace all floating-point numbers in an array of a particular type
                # (in this case CutsceneData) with their corresponding IEEE-754 hexadecimal representation
                if cutscene_data_regexpr.search(line) is not None:
                    is_cutscene_data = True
                elif line.endswith("};"):
                    is_cutscene_data = False
                if is_cutscene_data:
                    raw_line = re.sub(float_regexpr, repl_float_hex, raw_line)
            output_lines[-1] = raw_line

    if print_source:
        if isinstance(print_source, StringIO):
            for line in output_lines:
                print_source.write(line + '\n')
        else:
            newline_encoded = output_enc.encode("\n")
            for line in output_lines:
                try:
                    line_encoded = output_enc.encode(line)
                except UnicodeEncodeError:
                    print("Failed to encode a line to", output_enc)
                    print("The line:", line)
                    print("The line, utf-8-encoded:", line.encode("utf-8"))
                    raise
                print_source.write(line_encoded)
                print_source.write(newline_encoded)
            print_source.flush()

    return asm_functions

def fixup_objfile(objfile_name, functions, asm_prelude, assembler, output_enc, drop_mdebug_gptab, convert_statics):
    SECTIONS = ['.data', '.text', '.rodata', '.bss']

    with open(objfile_name, 'rb') as f:
        objfile = ElfFile(f.read())
    fmt = objfile.fmt

    prev_locs = {
        '.text': 0,
        '.data': 0,
        '.rodata': 0,
        '.bss': 0,
    }
    to_copy = {
        '.text': [],
        '.data': [],
        '.rodata': [],
        '.bss': [],
    }
    asm = []
    all_late_rodata_dummy_bytes = []
    all_jtbl_rodata_size = []
    late_rodata_asm = []
    late_rodata_source_name_start = None
    late_rodata_source_name_end = None

    # Generate an assembly file with all the assembly we need to fill in. For
    # simplicity we pad with nops/.space so that addresses match exactly, so we
    # don't have to fix up relocations/symbol references.
    all_text_glabels = set()
    func_sizes = {}
    for function in functions:
        ifdefed = False
        for sectype, (temp_name, size) in function.data.items():
            if temp_name is None:
                continue
            assert size > 0
            loc = objfile.find_symbol(temp_name)
            if loc is None:
                ifdefed = True
                break
            loc = loc[1]
            prev_loc = prev_locs[sectype]
            if loc < prev_loc:
                # If the dummy C generates too little asm, and we have two
                # consecutive GLOBAL_ASM blocks, we detect that error here.
                # On the other hand, if it generates too much, we don't have
                # a good way of discovering that error: it's indistinguishable
                # from a static symbol occurring after the GLOBAL_ASM block.
                raise Failure("Wrongly computed size for section {} (diff {}). This is an asm-processor bug!".format(sectype, prev_loc- loc))
            if loc != prev_loc:
                asm.append('.section ' + sectype)
                if sectype == '.text':
                    for i in range((loc - prev_loc) // 4):
                        asm.append('nop')
                else:
                    asm.append('.space {}'.format(loc - prev_loc))
            to_copy[sectype].append((loc, size, temp_name, function.fn_desc))
            if function.text_glabels and sectype == '.text':
                func_sizes[function.text_glabels[0]] = size
            prev_locs[sectype] = loc + size
        if not ifdefed:
            all_text_glabels.update(function.text_glabels)
            all_late_rodata_dummy_bytes.append(function.late_rodata_dummy_bytes)
            all_jtbl_rodata_size.append(function.jtbl_rodata_size)
            late_rodata_asm.append(function.late_rodata_asm_conts)
            for sectype, (temp_name, size) in function.data.items():
                if temp_name is not None:
                    asm.append('.section ' + sectype)
                    asm.append('glabel ' + temp_name + '_asm_start')
            asm.append('.text')
            for line in function.asm_conts:
                asm.append(line)
            for sectype, (temp_name, size) in function.data.items():
                if temp_name is not None:
                    asm.append('.section ' + sectype)
                    asm.append('glabel ' + temp_name + '_asm_end')
    if any(late_rodata_asm):
        late_rodata_source_name_start = '_asmpp_late_rodata_start'
        late_rodata_source_name_end = '_asmpp_late_rodata_end'
        asm.append('.section .late_rodata')
        # Put some padding at the start to avoid conflating symbols with
        # references to the whole section.
        asm.append('.word 0, 0')
        asm.append('glabel {}'.format(late_rodata_source_name_start))
        for conts in late_rodata_asm:
            asm.extend(conts)
        asm.append('glabel {}'.format(late_rodata_source_name_end))

    o_file = tempfile.NamedTemporaryFile(prefix='asm-processor', suffix='.o', delete=False)
    o_name = o_file.name
    o_file.close()
    s_file = tempfile.NamedTemporaryFile(prefix='asm-processor', suffix='.s', delete=False)
    s_name = s_file.name
    try:
        s_file.write(asm_prelude + b'\n')
        for line in asm:
            s_file.write(output_enc.encode(line) + b'\n')
        s_file.close()
        ret = os.system(assembler + " " + s_name + " -o " + o_name)
        if ret != 0:
            raise Failure("failed to assemble")
        with open(o_name, 'rb') as f:
            asm_objfile = ElfFile(f.read())

        # Remove clutter from objdump output for tests, and make the tests
        # portable by avoiding absolute paths. Outside of tests .mdebug is
        # useful for showing source together with asm, though.
        mdebug_section = objfile.find_section('.mdebug')
        if drop_mdebug_gptab:
            objfile.drop_mdebug_gptab()

        # Unify reginfo sections
        target_reginfo = objfile.find_section('.reginfo')
        if target_reginfo is not None:
            source_reginfo_data = list(asm_objfile.find_section('.reginfo').data)
            data = list(target_reginfo.data)
            for i in range(20):
                data[i] |= source_reginfo_data[i]
            target_reginfo.data = bytes(data)

        # Move over section contents
        modified_text_positions = set()
        jtbl_rodata_positions = set()
        last_rodata_pos = 0
        for sectype in SECTIONS:
            if not to_copy[sectype]:
                continue
            source = asm_objfile.find_section(sectype)
            assert source is not None, "didn't find source section: " + sectype
            for (pos, count, temp_name, fn_desc) in to_copy[sectype]:
                loc1 = asm_objfile.find_symbol_in_section(temp_name + '_asm_start', source)
                loc2 = asm_objfile.find_symbol_in_section(temp_name + '_asm_end', source)
                assert loc1 == pos, "assembly and C files don't line up for section " + sectype + ", " + fn_desc
                if loc2 - loc1 != count:
                    raise Failure("incorrectly computed size for section " + sectype + ", " + fn_desc + ". If using .double, make sure to provide explicit alignment padding.")
            if sectype == '.bss':
                continue
            target = objfile.find_section(sectype)
            assert target is not None, "missing target section of type " + sectype
            data = list(target.data)
            for (pos, count, _, _) in to_copy[sectype]:
                data[pos:pos + count] = source.data[pos:pos + count]
                if sectype == '.text':
                    assert count % 4 == 0
                    assert pos % 4 == 0
                    for i in range(count // 4):
                        modified_text_positions.add(pos + 4 * i)
                elif sectype == '.rodata':
                    last_rodata_pos = pos + count
            target.data = bytes(data)

        # Move over late rodata. This is heuristic, sadly, since I can't think
        # of another way of doing it.
        moved_late_rodata = {}
        if any(all_late_rodata_dummy_bytes) or any(all_jtbl_rodata_size):
            source = asm_objfile.find_section('.late_rodata')
            target = objfile.find_section('.rodata')
            source_pos = asm_objfile.find_symbol_in_section(late_rodata_source_name_start, source)
            source_end = asm_objfile.find_symbol_in_section(late_rodata_source_name_end, source)
            if source_end - source_pos != sum(map(len, all_late_rodata_dummy_bytes)) * 4 + sum(all_jtbl_rodata_size):
                raise Failure("computed wrong size of .late_rodata")
            new_data = list(target.data)
            for dummy_bytes_list, jtbl_rodata_size in zip(all_late_rodata_dummy_bytes, all_jtbl_rodata_size):
                for index, dummy_bytes in enumerate(dummy_bytes_list):
                    if not fmt.is_big_endian:
                        dummy_bytes = dummy_bytes[::-1]
                    pos = target.data.index(dummy_bytes, last_rodata_pos)
                    # This check is nice, but makes time complexity worse for large files:
                    if SLOW_CHECKS and target.data.find(dummy_bytes, pos + 4) != -1:
                        raise Failure("multiple occurrences of late_rodata hex magic. Change asm-processor to use something better than 0xE0123456!")
                    if index == 0 and len(dummy_bytes_list) > 1 and target.data[pos+4:pos+8] == b'\0\0\0\0':
                        # Ugly hack to handle double alignment for non-matching builds.
                        # We were told by .late_rodata_alignment (or deduced from a .double)
                        # that a function's late_rodata started out 4 (mod 8), and emitted
                        # a float and then a double. But it was actually 0 (mod 8), so our
                        # double was moved by 4 bytes. To make them adjacent to keep jump
                        # tables correct, move the float by 4 bytes as well.
                        new_data[pos:pos+4] = b'\0\0\0\0'
                        pos += 4
                    new_data[pos:pos+4] = source.data[source_pos:source_pos+4]
                    moved_late_rodata[source_pos] = pos
                    last_rodata_pos = pos + 4
                    source_pos += 4
                if jtbl_rodata_size > 0:
                    assert dummy_bytes_list, "should always have dummy bytes before jtbl data"
                    pos = last_rodata_pos
                    new_data[pos : pos + jtbl_rodata_size] = \
                        source.data[source_pos : source_pos + jtbl_rodata_size]
                    for i in range(0, jtbl_rodata_size, 4):
                        moved_late_rodata[source_pos + i] = pos + i
                        jtbl_rodata_positions.add(pos + i)
                    last_rodata_pos += jtbl_rodata_size
                    source_pos += jtbl_rodata_size
            target.data = bytes(new_data)

        # Merge strtab data.
        strtab_adj = len(objfile.sym_strtab.data)
        objfile.sym_strtab.data += asm_objfile.sym_strtab.data

        # Find relocated symbols
        relocated_symbols = set()
        for sectype in SECTIONS + ['.late_rodata']:
            sec = asm_objfile.find_section(sectype)
            if sec is None:
                continue
            for reltab in sec.relocated_by:
                for rel in reltab.relocations:
                    relocated_symbols.add(asm_objfile.symbol_entries[rel.sym_index])

        # Move over symbols, deleting the temporary function labels.
        # Skip over new local symbols that aren't relocated against, to
        # avoid conflicts.
        empty_symbol = objfile.symbol_entries[0]
        new_syms = [s for s in objfile.symbol_entries[1:] if not is_temp_name(s.name)]

        for i, s in enumerate(asm_objfile.symbol_entries):
            is_local = (i < asm_objfile.symtab.sh_info)
            if is_local and s not in relocated_symbols:
                continue
            if is_temp_name(s.name):
                assert s not in relocated_symbols
                continue
            if s.st_shndx not in [SHN_UNDEF, SHN_ABS]:
                section_name = asm_objfile.sections[s.st_shndx].name
                target_section_name = section_name
                if section_name == ".late_rodata":
                    target_section_name = ".rodata"
                elif section_name not in SECTIONS:
                    raise Failure("generated assembly .o must only have symbols for .text, .data, .rodata, .late_rodata, ABS and UNDEF, but found " + section_name)
                objfile_section = objfile.find_section(target_section_name)
                if objfile_section is None:
                    raise Failure("generated assembly .o has section that real objfile lacks: " + target_section_name)
                s.st_shndx = objfile_section.index
                # glabel's aren't marked as functions, making objdump output confusing. Fix that.
                if s.name in all_text_glabels:
                    s.st_type = STT_FUNC
                    if s.name in func_sizes:
                        s.st_size = func_sizes[s.name]
                if section_name == '.late_rodata':
                    if s.st_value == 0:
                        # This must be a symbol corresponding to the whole .late_rodata
                        # section, being referred to from a relocation.
                        # Moving local symbols is tricky, because it requires fixing up
                        # lo16/hi16 relocation references to .late_rodata+<offset>.
                        # Just disallow it for now.
                        raise Failure("local symbols in .late_rodata are not allowed")
                    s.st_value = moved_late_rodata[s.st_value]
            s.st_name += strtab_adj
            new_syms.append(s)
        make_statics_global = convert_statics in ("global", "global-with-filename")

        # Add static symbols from .mdebug, so they can be referred to from GLOBAL_ASM
        if mdebug_section and convert_statics != "no":
            static_name_count = {}
            strtab_index = len(objfile.sym_strtab.data)
            new_strtab_data = []
            ifd_max, cb_fd_offset = fmt.unpack('II', mdebug_section.data[18*4 : 20*4])
            cb_sym_offset, = fmt.unpack('I', mdebug_section.data[9*4 : 10*4])
            cb_ss_offset, = fmt.unpack('I', mdebug_section.data[15*4 : 16*4])
            for i in range(ifd_max):
                offset = cb_fd_offset + 18*4*i
                iss_base, _, isym_base, csym = fmt.unpack('IIII', objfile.data[offset + 2*4 : offset + 6*4])
                scope_level = 0
                for j in range(csym):
                    offset2 = cb_sym_offset + 12 * (isym_base + j)
                    iss, value, st_sc_index = fmt.unpack('III', objfile.data[offset2 : offset2 + 12])
                    st = (st_sc_index >> 26)
                    sc = (st_sc_index >> 21) & 0x1f
                    if st in (MIPS_DEBUG_ST_STATIC, MIPS_DEBUG_ST_STATIC_PROC):
                        symbol_name_offset = cb_ss_offset + iss_base + iss
                        symbol_name_offset_end = objfile.data.find(b'\0', symbol_name_offset)
                        assert symbol_name_offset_end != -1
                        symbol_name = objfile.data[symbol_name_offset : symbol_name_offset_end]
                        if scope_level > 1:
                            # For in-function statics, append an increasing counter to
                            # the name, to avoid duplicate conflicting symbols.
                            count = static_name_count.get(symbol_name, 0) + 1
                            static_name_count[symbol_name] = count
                            symbol_name += b":" + str(count).encode("utf-8")
                        emitted_symbol_name = symbol_name
                        if convert_statics == "global-with-filename":
                            # Change the emitted symbol name to include the filename,
                            # but don't let that affect deduplication logic (we still
                            # want to be able to reference statics from GLOBAL_ASM).
                            emitted_symbol_name = objfile_name.encode("utf-8") + b":" + symbol_name
                        section_name = {1: '.text', 2: '.data', 3: '.bss', 15: '.rodata'}[sc]
                        section = objfile.find_section(section_name)
                        symtype = STT_FUNC if sc == 1 else STT_OBJECT
                        binding = STB_GLOBAL if make_statics_global else STB_LOCAL
                        sym = Symbol.from_parts(
                            fmt,
                            st_name=strtab_index,
                            st_value=value,
                            st_size=0,
                            st_info=(binding << 4 | symtype),
                            st_other=STV_DEFAULT,
                            st_shndx=section.index,
                            strtab=objfile.sym_strtab,
                            name=symbol_name.decode('latin1'))
                        strtab_index += len(emitted_symbol_name) + 1
                        new_strtab_data.append(emitted_symbol_name + b'\0')
                        new_syms.append(sym)
                    if st in (
                        MIPS_DEBUG_ST_FILE,
                        MIPS_DEBUG_ST_STRUCT,
                        MIPS_DEBUG_ST_UNION,
                        MIPS_DEBUG_ST_ENUM,
                        MIPS_DEBUG_ST_BLOCK,
                        MIPS_DEBUG_ST_PROC,
                        MIPS_DEBUG_ST_STATIC_PROC,
                    ):
                        scope_level += 1
                    if st == MIPS_DEBUG_ST_END:
                        scope_level -= 1
                assert scope_level == 0
            objfile.sym_strtab.data += b''.join(new_strtab_data)

        # Get rid of duplicate symbols, favoring ones that are not UNDEF.
        # Skip this for unnamed local symbols though.
        new_syms.sort(key=lambda s: 0 if s.st_shndx != SHN_UNDEF else 1)
        old_syms = []
        newer_syms = []
        name_to_sym = {}
        for s in new_syms:
            if s.name == "_gp_disp":
                s.st_type = STT_OBJECT
            if s.st_bind == STB_LOCAL and s.st_shndx == SHN_UNDEF:
                raise Failure("local symbol \"" + s.name + "\" is undefined")
            if not s.name:
                if s.st_bind != STB_LOCAL:
                    raise Failure("global symbol with no name")
                newer_syms.append(s)
            else:
                existing = name_to_sym.get(s.name)
                if not existing:
                    name_to_sym[s.name] = s
                    newer_syms.append(s)
                elif s.st_shndx != SHN_UNDEF and not (
                    existing.st_shndx == s.st_shndx and existing.st_value == s.st_value
                ):
                    raise Failure("symbol \"" + s.name + "\" defined twice")
                else:
                    s.replace_by = existing
                    old_syms.append(s)
        new_syms = newer_syms

        # Put local symbols in front, with the initial dummy entry first, and
        # _gp_disp at the end if it exists.
        new_syms.insert(0, empty_symbol)
        new_syms.sort(key=lambda s: (s.st_bind != STB_LOCAL, s.name == "_gp_disp"))
        num_local_syms = sum(1 for s in new_syms if s.st_bind == STB_LOCAL)

        for i, s in enumerate(new_syms):
            s.new_index = i
        for s in old_syms:
            s.new_index = s.replace_by.new_index
        objfile.symtab.data = b''.join(s.to_bin() for s in new_syms)
        objfile.symtab.sh_info = num_local_syms

        # Fix up relocation symbol references
        for sectype in SECTIONS:
            target = objfile.find_section(sectype)

            if target is not None:
                # fixup relocation symbol indices, since we butchered them above
                for reltab in target.relocated_by:
                    nrels = []
                    for rel in reltab.relocations:
                        if (sectype == '.text' and rel.r_offset in modified_text_positions or
                            sectype == '.rodata' and rel.r_offset in jtbl_rodata_positions):
                            # don't include relocations for late_rodata dummy code
                            continue
                        rel.sym_index = objfile.symbol_entries[rel.sym_index].new_index
                        nrels.append(rel)
                    reltab.relocations = nrels
                    reltab.data = b''.join(rel.to_bin() for rel in nrels)

        # Move over relocations
        for sectype in SECTIONS + ['.late_rodata']:
            source = asm_objfile.find_section(sectype)
            if source is None or not source.data:
                continue

            target_sectype = '.rodata' if sectype == '.late_rodata' else sectype
            target = objfile.find_section(target_sectype)
            assert target is not None, target_sectype
            for reltab in source.relocated_by:
                for rel in reltab.relocations:
                    rel.sym_index = asm_objfile.symbol_entries[rel.sym_index].new_index
                    if sectype == '.late_rodata':
                        rel.r_offset = moved_late_rodata[rel.r_offset]
                new_data = b''.join(rel.to_bin() for rel in reltab.relocations)
                prefix, sh_entsize = ('.rel', 8) if reltab.sh_type == SHT_REL else ('.rela', 12)
                target_reltab = objfile.find_section(prefix + target_sectype)
                if not target_reltab:
                    target_reltab = objfile.add_section(prefix + target_sectype,
                            sh_type=reltab.sh_type, sh_flags=0,
                            sh_link=objfile.symtab.index, sh_info=target.index,
                            sh_addralign=4, sh_entsize=sh_entsize, data=b'')
                target_reltab.data += new_data

        objfile.write(objfile_name)
    finally:
        s_file.close()
        os.remove(s_name)
        try:
            os.remove(o_name)
        except:
            pass

def run_wrapped(argv, outfile, functions):
    dir_path = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="Pre-process .c files and post-process .o files to enable embedding assembly into C.")
    parser.add_argument('filename', help="path to .c code")
    parser.add_argument('--post-process', dest='objfile', help="path to .o file to post-process")
    parser.add_argument('--assembler', dest='assembler', help="assembler command (e.g. \"mips-linux-gnu-as -march=vr4300 -mabi=32\")")
    parser.add_argument('--asm-prelude', dest='asm_prelude', type=Path, default=dir_path / "prelude.inc", help="path to a file containing a prelude to the assembly file (with .set and .macro directives, e.g.)")
    parser.add_argument('--input-enc', default='latin1', help="input encoding (default: %(default)s)")
    parser.add_argument('--output-enc', default='latin1', help="output encoding (default: %(default)s)")
    parser.add_argument('--drop-mdebug-gptab', dest='drop_mdebug_gptab', action='store_true', help="drop mdebug and gptab sections")
    parser.add_argument('--convert-statics', dest='convert_statics', choices=["no", "local", "global", "global-with-filename"], default="local", help="change static symbol visibility (default: %(default)s)")
    parser.add_argument('--force', dest='force', action='store_true', help="force processing of files without GLOBAL_ASM blocks")
    parser.add_argument('--keep-preprocessed', dest='keep_output_dir', type=Path, help="emit temporary files to this directory (build.py only)")
    parser.add_argument('--no-dep-file', action='store_true', help="don't generate a .d make dependency file (build.py only)")
    parser.add_argument('--encode-cutscene-data-floats', dest='encode_cutscene_data_floats', action='store_true', default=False, help="Replace floats with their encoded hexadecimal representation in CutsceneData data")
    parser.add_argument('-framepointer', dest='framepointer', action='store_true')
    parser.add_argument('-mips1', dest='mips1', action='store_true')
    parser.add_argument('-g3', dest='g3', action='store_true')
    parser.add_argument('-KPIC', dest='kpic', action='store_true')
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('-O0', dest='opt', action='store_const', const='O0')
    group.add_argument('-O1', dest='opt', action='store_const', const='O1')
    group.add_argument('-O2', dest='opt', action='store_const', const='O2')
    group.add_argument('-g', dest='opt', action='store_const', const='g')
    args = parser.parse_args(argv)
    opt = args.opt
    pascal = any(args.filename.endswith(ext) for ext in (".p", ".pas", ".pp"))
    if args.g3:
        if opt != 'O2':
            raise Failure("-g3 is only supported together with -O2")
        opt = 'g3'
    if args.mips1 and (opt not in ('O1', 'O2') or args.framepointer):
        raise Failure("-mips1 is only supported together with -O1 or -O2")
    if pascal and opt not in ('O1', 'O2', 'g3'):
        raise Failure("Pascal is only supported together with -O1, -O2 or -O2 -g3")
    output_enc = Encoding(args.output_enc)
    opts = Opts(opt, args.framepointer, args.mips1, args.kpic, pascal, args.input_enc, output_enc, args.encode_cutscene_data_floats)

    if args.objfile is None:
        with open(args.filename, encoding=args.input_enc) as f:
            deps = []
            functions = parse_source(f, opts, out_dependencies=deps, print_source=outfile)
            return functions, deps, args.keep_output_dir
    else:
        if args.assembler is None:
            raise Failure("must pass assembler command")
        if functions is None:
            with open(args.filename, encoding=args.input_enc) as f:
                functions = parse_source(f, opts, out_dependencies=[])
        if not functions and not args.force:
            return
        asm_prelude = b''
        if args.asm_prelude:
            with open(args.asm_prelude, 'rb') as f:
                asm_prelude = f.read()
        fixup_objfile(args.objfile, functions, asm_prelude, args.assembler, output_enc, args.drop_mdebug_gptab, args.convert_statics)

def run(argv, outfile=sys.stdout.buffer, functions=None):
    try:
        return run_wrapped(argv, outfile, functions)
    except Failure as e:
        print("Error:", e, file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    run(sys.argv[1:])
