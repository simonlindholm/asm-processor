use std::{
    fs::File,
    io::{BufWriter, Cursor, Seek, SeekFrom, Write},
    path::PathBuf,
};

use binrw::{binrw, BinRead, BinResult, BinWrite, Endian};
use encoding_rs::WINDOWS_1252;

const EI_NIDENT: usize = 16;
const EI_CLASS: u32 = 4;
const EI_DATA: u32 = 5;
const EI_VERSION: u32 = 6;
const EI_OSABI: u32 = 7;
const EI_ABIVERSION: u32 = 8;
const STN_UNDEF: u32 = 0;

const SHN_UNDEF: u16 = 0;
const SHN_ABS: u16 = 0xfff1;
const SHN_COMMON: u16 = 0xfff2;
const SHN_XINDEX: u16 = 0xffff;
const SHN_LORESERVE: u16 = 0xff00;

const STT_NOTYPE: u8 = 0;
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;
const STT_FILE: u8 = 4;
const STT_COMMON: u8 = 5;
const STT_TLS: u8 = 6;

const STB_LOCAL: u32 = 0;
const STB_GLOBAL: u32 = 1;
const STB_WEAK: u32 = 2;

const STV_DEFAULT: u8 = 0;
const STV_INTERNAL: u8 = 1;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;

const SHT_NULL: u32 = 0;
const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_HASH: u32 = 5;
const SHT_DYNAMIC: u32 = 6;
const SHT_NOTE: u32 = 7;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHT_SHLIB: u32 = 10;
const SHT_DYNSYM: u32 = 11;
const SHT_INIT_ARRAY: u32 = 14;
const SHT_FINI_ARRAY: u32 = 15;
const SHT_PREINIT_ARRAY: u32 = 16;
const SHT_GROUP: u32 = 17;
const SHT_SYMTAB_SHNDX: u32 = 18;
const SHT_MIPS_GPTAB: u32 = 0x70000003;
const SHT_MIPS_DEBUG: u32 = 0x70000005;
const SHT_MIPS_REGINFO: u32 = 0x70000006;
const SHT_MIPS_OPTIONS: u32 = 0x7000000d;

const SHF_WRITE: u32 = 0x1;
const SHF_ALLOC: u32 = 0x2;
const SHF_EXECINSTR: u32 = 0x4;
const SHF_MERGE: u32 = 0x10;
const SHF_STRINGS: u32 = 0x20;
const SHF_INFO_LINK: u32 = 0x40;
const SHF_LINK_ORDER: u32 = 0x80;
const SHF_OS_NONCONFORMING: u32 = 0x100;
const SHF_GROUP: u32 = 0x200;
const SHF_TLS: u32 = 0x400;

const R_MIPS_32: u32 = 2;
const R_MIPS_26: u32 = 4;
const R_MIPS_HI16: u32 = 5;
const R_MIPS_LO16: u32 = 6;

const MIPS_DEBUG_ST_STATIC: u32 = 2;
const MIPS_DEBUG_ST_PROC: u32 = 6;
const MIPS_DEBUG_ST_BLOCK: u32 = 7;
const MIPS_DEBUG_ST_END: u32 = 8;
const MIPS_DEBUG_ST_FILE: u32 = 11;
const MIPS_DEBUG_ST_STATIC_PROC: u32 = 14;
const MIPS_DEBUG_ST_STRUCT: u32 = 26;
const MIPS_DEBUG_ST_UNION: u32 = 27;
const MIPS_DEBUG_ST_ENUM: u32 = 28;

#[binrw]
struct ElfHeader {
    e_ident: [u8; EI_NIDENT],
    e_type: u16,
    e_machine: u16,
    e_version: u32,
    e_entry: u32,
    e_phoff: u32,
    e_shoff: u32,
    e_flags: u32,
    e_ehsize: u16,
    e_phentsize: u16,
    e_phnum: u16,
    e_shentsize: u16,
    e_shnum: u16,
    e_shstrndx: u16,
}

impl ElfHeader {
    const SIZE: usize = 52;

    fn new(data: &[u8], endian: Endian) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let header = Self::read_options(&mut cursor, endian, ())?;

        assert_eq!(header.e_ident[EI_CLASS as usize], 1);
        assert_eq!(header.e_type, 1); // relocatable
        assert_eq!(header.e_machine, 8); // MIPS I Architecture
        assert_eq!(header.e_phoff, 0); // no program header
        assert_ne!(header.e_shoff, 0); // section header
        assert_ne!(header.e_shstrndx, SHN_UNDEF);

        Ok(header)
    }

    fn to_bin(&self, endian: Endian) -> BinResult<[u8; Self::SIZE]> {
        let mut rv = [0; Self::SIZE];
        let mut cursor = Cursor::new(rv.as_mut_slice());

        self.write_options(&mut cursor, endian, ())?;
        Ok(rv)
    }
}

#[binrw]
#[derive(Clone, PartialEq, Eq, Hash)]
struct SymbolData {
    pub st_name: u32,
    pub st_value: u32,
    pub st_size: u32,
    st_info: u8,
    st_other: u8,
    pub st_shndx: u16,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Symbol {
    pub data: SymbolData,
    bind: u8,
    pub typ: u8,
    pub name: String,
    visibility: u8,
}

impl Symbol {
    fn new(
        data: &[u8],
        strtab: Option<&Section>,
        name: Option<String>,
        endian: Endian,
    ) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let data = SymbolData::read_options(&mut cursor, endian, ())?;
        assert_ne!(data.st_shndx, SHN_XINDEX);
        let bind = data.st_info >> 4;
        let typ = data.st_info & 0xf;
        let name = name.unwrap_or_else(|| strtab.unwrap().lookup_str(data.st_name as usize));
        let visibility = data.st_other & 0x3;

        Ok(Self {
            data,
            bind,
            typ,
            name,
            visibility,
        })
    }

    pub fn from_parts(
        st_name: u32,
        st_value: u32,
        st_size: u32,
        st_info: u8,
        st_other: u8,
        st_shndx: u16,
        name: &str,
        endian: Endian,
    ) -> BinResult<Self> {
        let header = SymbolData {
            st_name,
            st_value,
            st_size,
            st_info,
            st_other,
            st_shndx,
        };
        let mut rv = [0; 16];
        let mut cursor = Cursor::new(rv.as_mut_slice());
        header.write_options(&mut cursor, endian, ())?;

        Symbol::new(&rv, None, Some(name.to_string()), endian)
    }
}

#[binrw]
#[derive(Clone)]
struct RelocationData {
    r_offset: u32,
    r_info: u32,
    r_addend: Option<u32>,
}

#[derive(Clone)]
struct Relocation {
    sh_type: u32,
    data: RelocationData,
}

impl Relocation {
    fn new(data: &[u8], sh_type: u32, endian: Endian) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let data = RelocationData::read_options(&mut cursor, endian, ())?;

        Ok(Self { sh_type, data })
    }

    fn to_bin(&self, endian: Endian) -> BinResult<Vec<u8>> {
        let mut rv = vec![];
        let mut cursor = Cursor::new(&mut rv);

        self.data.write_options(&mut cursor, endian, ())?;
        Ok(rv)
    }

    pub fn sym_index(&self) -> usize {
        (self.data.r_info >> 8) as usize
    }

    fn rel_type(&self) -> usize {
        (self.data.r_info & 0xff) as usize
    }
}

#[binrw]
struct HDRR {
    magic: u16,
    vstamp: u16,
    iline_max: u32,
    cb_line: u32,
    cb_line_offset: u32,
    idn_max: u32,
    cb_dn_offset: u32,
    ipd_max: u32,
    cb_pd_offset: u32,
    isym_max: u32,
    cb_sym_offset: u32,
    iopt_max: u32,
    cb_opt_offset: u32,
    iaux_max: u32,
    cb_aux_offset: u32,
    iss_max: u32,
    cb_ss_offset: u32,
    iss_ext_max: u32,
    cb_ss_ext_offset: u32,
    ifd_max: u32,
    cb_fd_offset: u32,
    crfd: u32,
    cb_rfd_offset: u32,
    iext_max: u32,
    cb_ext_offset: u32,
}

impl HDRR {
    const SIZE: usize = 96;
}

#[binrw]
#[derive(Clone)]
struct SectionHeader {
    sh_name: u32,
    sh_type: u32,
    sh_flags: u32,
    sh_addr: u32,
    sh_offset: u32,
    sh_size: u32,
    sh_link: u32,
    pub sh_info: u32,
    sh_addralign: u32,
    sh_entsize: u32,
}

impl SectionHeader {
    const SIZE: usize = 40;
}

#[derive(Clone)]
struct Section {
    pub header: SectionHeader,
    pub data: Vec<u8>,
    pub index: usize,
    pub relocated_by: Vec<usize>,
    rel_target: Option<usize>,
    pub symbol_entries: Vec<Symbol>,
    pub relocations: Vec<Relocation>,
    pub name: Option<String>,
    pub strtab: Option<usize>,
}

impl Section {
    fn new(data: &[u8], other_data: &[u8], index: usize, endian: Endian) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let header = SectionHeader::read_options(&mut cursor, endian, ())?;
        assert!(!(header.sh_flags & SHF_LINK_ORDER != 0));
        if header.sh_entsize != 0 {
            assert_eq!(header.sh_size % header.sh_entsize, 0);
        }

        let data = if header.sh_type == SHT_NOBITS {
            vec![]
        } else {
            other_data[header.sh_offset as usize..(header.sh_offset + header.sh_size) as usize]
                .to_vec()
        };
        Ok(Self {
            header,
            data,
            index,
            relocated_by: vec![],
            rel_target: None,
            symbol_entries: vec![],
            relocations: vec![],
            name: None,
            strtab: None,
        })
    }

    fn from_parts(
        sh_name: u32,
        sh_type: u32,
        sh_flags: u32,
        sh_link: u32,
        sh_info: u32,
        sh_addralign: u32,
        sh_entsize: u32,
        data: &[u8],
        index: usize,
        endian: Endian,
    ) -> BinResult<Self> {
        let header = SectionHeader {
            sh_name,
            sh_type,
            sh_flags,
            sh_addr: 0,
            sh_offset: 0,
            sh_size: data.len() as u32,
            sh_link,
            sh_info,
            sh_addralign,
            sh_entsize,
        };

        let mut rv = [0; SectionHeader::SIZE];
        let mut cursor = Cursor::new(rv.as_mut_slice());

        header.write_options(&mut cursor, endian, ())?;

        Self::new(&rv, data, index, endian)
    }

    fn lookup_str(&self, index: usize) -> String {
        assert_eq!(self.header.sh_type, SHT_STRTAB);
        let to = self
            .data
            .iter()
            .skip(index)
            .position(|&x| x == 0)
            .unwrap_or(self.data.len()) // TODO should panic, not "or"
            + index;
        let line = WINDOWS_1252.decode_without_bom_handling(&self.data[index..to]);
        let line = line.0.into_owned();
        line
    }

    fn add_str(&mut self, string: &str) -> u32 {
        assert_eq!(self.header.sh_type, SHT_STRTAB);
        let index = self.data.len() as u32;

        let data = WINDOWS_1252.encode(string).0;
        self.data.extend_from_slice(&data);
        self.data.push(0);
        index
    }

    fn is_rel(&self) -> bool {
        self.header.sh_type == SHT_REL || self.header.sh_type == SHT_RELA
    }

    fn header_to_bin(&mut self, endian: Endian) -> BinResult<[u8; SectionHeader::SIZE]> {
        if self.header.sh_type != SHT_NOBITS {
            self.header.sh_size = self.data.len() as u32;
        }

        let mut rv = [0; SectionHeader::SIZE];
        let mut cursor = Cursor::new(rv.as_mut_slice());

        self.header.write_options(&mut cursor, endian, ())?;

        Ok(rv)
    }

    fn late_init(&mut self, sections: &mut [Section], endian: Endian) {
        if self.header.sh_type == SHT_SYMTAB {
            self.init_symbols(sections, endian);
        } else if self.is_rel() {
            let s: &mut Section = sections.get_mut(self.header.sh_info as usize).unwrap();

            self.rel_target = Some(s.index);
            s.relocated_by.push(self.index);
            self.init_relocs(endian);
        }
    }

    pub fn find_symbol(&self, name: &str) -> Option<(u16, u32)> {
        assert_eq!(self.header.sh_type, SHT_SYMTAB);
        for s in &self.symbol_entries {
            if s.name == name {
                return Some((s.data.st_shndx, s.data.st_value));
            }
        }
        None
    }

    pub fn find_symbol_in_section(&self, name: &str, section: &Section) -> Option<u32> {
        let (st_shndx, st_value) = self.find_symbol(name)?;
        assert_eq!(st_shndx, section.index as u16);
        Some(st_value)
    }

    fn init_symbols(&mut self, sections: &[Section], endian: Endian) {
        assert_eq!(self.header.sh_type, SHT_SYMTAB);
        assert_eq!(self.header.sh_entsize, 16);

        let strtab = sections.get(self.header.sh_link as usize).unwrap();
        self.strtab = Some(strtab.index);

        for i in 0..(self.data.len() / 16) {
            let symbol =
                Symbol::new(&self.data[i * 16..(i + 1) * 16], strtab, None, endian).unwrap();
            self.symbol_entries.push(symbol);
        }
    }

    fn init_relocs(&mut self, endian: Endian) {
        assert!(self.is_rel());

        let mut entries = vec![];
        for i in (0..self.header.sh_size).step_by(self.header.sh_entsize as usize) {
            entries.push(
                Relocation::new(
                    &self.data[i as usize..(i + self.header.sh_entsize) as usize],
                    self.header.sh_type,
                    endian,
                )
                .unwrap(),
            );
        }
        self.relocations = entries;
    }

    fn local_symbols(&self) -> &[Symbol] {
        assert_eq!(self.header.sh_type, SHT_SYMTAB);
        &self.symbol_entries[..self.header.sh_info as usize]
    }

    fn global_symbols(&self) -> &[Symbol] {
        assert_eq!(self.header.sh_type, SHT_SYMTAB);
        &self.symbol_entries[self.header.sh_info as usize..]
    }

    fn relocate_mdebug(&mut self, original_offset: usize, endian: Endian) {
        assert_eq!(self.header.sh_type, SHT_MIPS_DEBUG);
        let shift_by = self.header.sh_offset as usize - original_offset;

        let mut hdrr = HDRR::read_options(&mut Cursor::new(&self.data), endian, ()).unwrap();

        assert_eq!(hdrr.magic, 0x7009);

        if hdrr.cb_line != 0 {
            hdrr.cb_line_offset += shift_by as u32;
        }
        if hdrr.idn_max != 0 {
            hdrr.cb_dn_offset += shift_by as u32;
        }
        if hdrr.ipd_max != 0 {
            hdrr.cb_pd_offset += shift_by as u32;
        }
        if hdrr.isym_max != 0 {
            hdrr.cb_sym_offset += shift_by as u32;
        }
        if hdrr.iopt_max != 0 {
            hdrr.cb_opt_offset += shift_by as u32;
        }
        if hdrr.iaux_max != 0 {
            hdrr.cb_aux_offset += shift_by as u32;
        }
        if hdrr.iss_max != 0 {
            hdrr.cb_ss_offset += shift_by as u32;
        }
        if hdrr.iss_ext_max != 0 {
            hdrr.cb_ss_ext_offset += shift_by as u32;
        }
        if hdrr.ifd_max != 0 {
            hdrr.cb_fd_offset += shift_by as u32;
        }
        if hdrr.crfd != 0 {
            hdrr.cb_rfd_offset += shift_by as u32;
        }
        if hdrr.iext_max != 0 {
            hdrr.cb_ext_offset += shift_by as u32;
        }

        let mut new_data = [0; HDRR::SIZE];
        let mut cursor = Cursor::new(new_data.as_mut_slice());
        hdrr.write_options(&mut cursor, endian, ());

        self.data = new_data.to_vec();
    }
}

pub struct ElfFile {
    pub data: Vec<u8>,
    pub endian: Endian,
    header: ElfHeader,
    pub sections: Vec<Section>,
    symtab: Option<usize>,
}

impl ElfFile {
    pub fn new(data: &[u8]) -> BinResult<Self> {
        let data = data.to_vec();
        assert_eq!(data[..4], [0x7f, b'E', b'L', b'F']);

        let endian: Endian = if data[5] == 1 {
            Endian::Little
        } else if data[5] == 2 {
            Endian::Big
        } else {
            panic!("Invalid ELF endianness");
        };
        let header = ElfHeader::new(&data[..ElfHeader::SIZE], endian).unwrap();
        let offset = header.e_shoff as usize;
        let size = header.e_shentsize as usize;
        let null_section =
            Section::new(&data[offset as usize..offset + size], &data, 0, endian).unwrap();
        let num_sections = if header.e_shnum == 0 {
            null_section.header.sh_size as usize
        } else {
            header.e_shnum as usize
        };
        let mut sections = vec![null_section];

        for i in 1..num_sections {
            let ind = offset + i * size;
            let section = Section::new(&data[ind..ind + size], &data, i, endian).unwrap();
            sections.push(section);
        }

        let mut symtab = None;
        for s in &sections {
            if s.header.sh_type == SHT_SYMTAB {
                assert!(symtab.is_none());
                symtab = Some(s.index);
                break;
            }
        }
        assert!(symtab.is_some());

        let shstr = sections.get(header.e_shstrndx as usize).unwrap().clone();
        for s in sections.iter_mut() {
            s.name = Some(shstr.lookup_str(s.header.sh_name as usize));
            s.late_init(&mut sections, endian);
        }

        Ok(ElfFile {
            data,
            endian,
            header,
            sections,
            symtab,
        })
    }

    pub fn find_section(&self, name: &str) -> Option<&Section> {
        self.sections
            .iter()
            .find(|s| s.name.as_ref().unwrap() == name)
    }

    pub fn find_section_mut(&mut self, name: &str) -> Option<&mut Section> {
        self.sections
            .iter_mut()
            .find(|s| s.name.as_ref().unwrap() == name)
    }

    pub fn symtab(&self) -> &Section {
        self.sections.get(self.symtab.unwrap()).unwrap()
    }

    fn add_section(
        &mut self,
        name: &str,
        sh_type: u32,
        sh_flags: u32,
        sh_link: u32,
        sh_info: u32,
        sh_addralign: u32,
        sh_entsize: u32,
        data: &[u8],
        endian: Endian,
    ) -> &Section {
        let shstr = self
            .sections
            .get_mut(self.header.e_shstrndx as usize)
            .unwrap();
        let sh_name = shstr.add_str(name);
        let mut s = Section::from_parts(
            sh_name,
            sh_type,
            sh_flags,
            sh_link,
            sh_info,
            sh_addralign,
            sh_entsize,
            data,
            self.sections.len(),
            endian,
        )
        .unwrap();
        s.name = Some(name.to_string());
        s.late_init(&mut self.sections, endian);
        self.sections.push(s);

        &self.sections.last().unwrap()
    }

    pub fn drop_mdebug_gptab(&mut self) {
        // We can only drop sections at the end, since otherwise section
        // references might be wrong. Luckily, these sections typically are.
        while self.sections.last().unwrap().header.sh_type == SHT_MIPS_DEBUG
            || self.sections.last().unwrap().header.sh_type == SHT_MIPS_GPTAB
        {
            self.sections.pop();
        }
    }

    fn pad_out(writer: &mut BufWriter<&mut File>, align: usize) {
        let pos = writer.stream_position().unwrap() as usize;

        if align > 0 && pos % align != 0 {
            let pad = align - (pos % align);
            for _ in 0..pad {
                writer.write(&[0]).unwrap();
            }
        }
    }

    fn write(&mut self, filename: PathBuf) {
        let mut file = std::fs::File::create(filename).unwrap();
        let mut writer = BufWriter::new(&mut file);

        self.header.e_shnum = self.sections.len() as u16;
        writer
            .write(&self.header.to_bin(self.endian).unwrap())
            .unwrap();

        for s in &mut self.sections {
            if s.header.sh_type != SHT_NOBITS && s.header.sh_type != SHT_NULL {
                Self::pad_out(&mut writer, s.header.sh_addralign as usize);
                let old_offset = s.header.sh_offset;
                s.header.sh_offset = writer.stream_position().unwrap() as u32;
                if s.header.sh_type == SHT_MIPS_DEBUG && s.header.sh_offset != old_offset {
                    // The .mdebug section has moved, relocate offsets
                    s.relocate_mdebug(old_offset as usize, self.endian);
                }
                writer.write(&s.data).unwrap();
            }
        }

        Self::pad_out(&mut writer, 4);
        self.header.e_shoff = writer.stream_position().unwrap() as u32;

        for s in &mut self.sections {
            writer
                .write(&s.header_to_bin(self.endian).unwrap())
                .unwrap();
        }

        writer.seek(SeekFrom::Start(0)).unwrap();
        writer
            .write(&self.header.to_bin(self.endian).unwrap())
            .unwrap();
        writer.flush().unwrap();
    }
}
