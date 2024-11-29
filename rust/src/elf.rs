use anyhow::Result;
use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fs::{self, File},
    io::{BufWriter, Cursor, Seek, SeekFrom, Write},
    path::PathBuf,
    process::Command,
    rc::Rc,
};

use binrw::{binrw, BinRead, BinResult, BinWrite, Endian};
use encoding_rs::WINDOWS_1252;
use temp_dir::TempDir;

use crate::{Function, SymbolVisibility};

const EI_NIDENT: usize = 16;
const EI_CLASS: u32 = 4;
const EI_DATA: u32 = 5;

const SHN_UNDEF: u16 = 0;
const SHN_ABS: u16 = 0xfff1;
const SHN_XINDEX: u16 = 0xffff;

const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;

const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;

const STV_DEFAULT: u8 = 0;

const SHT_NULL: u32 = 0;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_REL: u32 = 9;
const SHT_MIPS_GPTAB: u32 = 0x70000003;
const SHT_MIPS_DEBUG: u32 = 0x70000005;

const SHF_LINK_ORDER: u32 = 0x80;

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
pub(crate) struct SymbolData {
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
    pub bind: u8,
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
        let name = name.unwrap_or_else(|| strtab.unwrap().lookup_str(data.st_name as usize));
        let visibility = data.st_other & 0x3;

        Ok(Self {
            data,
            bind,
            name,
            visibility,
        })
    }

    pub fn from_parts(header: SymbolData, name: &str, endian: Endian) -> BinResult<Self> {
        let mut rv = [0; 16];
        let mut cursor = Cursor::new(rv.as_mut_slice());
        header.write_options(&mut cursor, endian, ())?;

        Symbol::new(&rv, None, Some(name.to_string()), endian)
    }

    pub fn set_type(&mut self, typ: u8) {
        self.data.st_info = (self.bind << 4) | typ;
    }

    pub fn to_bin(&self) -> Vec<u8> {
        let mut rv = vec![];
        let mut cursor = Cursor::new(&mut rv);

        self.data
            .write_options(&mut cursor, Endian::Big, ())
            .unwrap();
        rv
    }
}

#[binrw]
#[derive(Clone)]
pub(crate) struct RelocationDataInner {
    pub r_offset: u32,
    r_info: u32,
}

#[binrw]
#[derive(Clone)]
pub(crate) struct RelocationData {
    inner: RelocationDataInner,
    r_addend: Option<u32>,
}

#[derive(Clone)]
pub(crate) struct Relocation {
    pub data: RelocationData,
}

impl Relocation {
    fn new(data: &[u8], sh_type: u32, endian: Endian) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let data = if data.len() < size_of::<RelocationData>() {
            let inner = RelocationDataInner::read_options(&mut cursor, endian, ())?;
            RelocationData {
                inner,
                r_addend: None,
            }
        } else {
            RelocationData::read_options(&mut cursor, endian, ())?
        };

        if sh_type == SHT_REL {
            assert!(data.r_addend.is_none());
        } else {
            assert!(data.r_addend.is_some());
        }

        Ok(Self { data })
    }

    pub fn to_bin(&self, endian: Endian) -> BinResult<Vec<u8>> {
        let mut rv = vec![];
        let mut cursor = Cursor::new(&mut rv);

        self.data.write_options(&mut cursor, endian, ())?;
        Ok(rv)
    }

    pub fn sym_index(&self) -> usize {
        (self.data.inner.r_info >> 8) as usize
    }

    pub fn set_sym_index(&mut self, index: usize) {
        self.data.inner.r_info = ((index as u32) << 8) | (self.data.inner.r_info & 0xff);
    }
}

#[binrw]
struct Hdrr {
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

impl Hdrr {
    const SIZE: usize = 96;
}

#[binrw]
#[derive(Clone)]
pub(crate) struct SectionHeader {
    sh_name: u32,
    pub sh_type: u32,
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
pub(crate) struct Section {
    pub header: SectionHeader,
    pub data: Vec<u8>,
    pub index: usize,
    pub relocated_by: Vec<usize>,
    rel_target: Option<usize>,
    pub symbol_entries: Vec<Rc<RefCell<Symbol>>>,
    pub relocations: Vec<Relocation>,
    pub name: Option<String>,
    pub strtab: Option<usize>,
}

impl Section {
    fn new(data: &[u8], other_data: &[u8], index: usize, endian: Endian) -> BinResult<Self> {
        let mut cursor = Cursor::new(data);

        let header = SectionHeader::read_options(&mut cursor, endian, ())?;
        assert!(header.sh_flags & SHF_LINK_ORDER == 0);
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
        let to = self.data.iter().skip(index).position(|&x| x == 0).unwrap() + index;
        let line = WINDOWS_1252.decode_without_bom_handling(&self.data[index..to]);
        line.0.into_owned()
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
            if s.borrow().name == name {
                return Some((s.borrow().data.st_shndx, s.borrow().data.st_value));
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
                Symbol::new(&self.data[i * 16..(i + 1) * 16], Some(strtab), None, endian).unwrap();
            self.symbol_entries.push(Rc::new(RefCell::new(symbol)));
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

    fn relocate_mdebug(&mut self, original_offset: usize, endian: Endian) -> BinResult<()> {
        assert_eq!(self.header.sh_type, SHT_MIPS_DEBUG);
        let shift_by = self.header.sh_offset as usize - original_offset;

        let mut hdrr = Hdrr::read_options(&mut Cursor::new(&self.data), endian, ()).unwrap();

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

        let mut new_data = [0; Hdrr::SIZE];
        let mut cursor = Cursor::new(new_data.as_mut_slice());
        hdrr.write_options(&mut cursor, endian, ())?;

        self.data = new_data.to_vec();
        Ok(())
    }
}

pub struct ElfFile {
    pub data: Vec<u8>,
    pub endian: Endian,
    header: ElfHeader,
    pub sections: Vec<Section>,
    symtab: Option<usize>,
}

struct ToCopyData {
    loc: u32,
    size: usize,
    temp_name: String,
    fn_desc: String,
}

impl ElfFile {
    pub fn new(data: &[u8]) -> BinResult<Self> {
        let data = data.to_vec();
        assert_eq!(data[..4], [0x7f, b'E', b'L', b'F']);

        let endian: Endian = if data[EI_DATA as usize] == 1 {
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
        let mut relocated_bys = vec![];

        let sections_before = sections.clone();

        for s in sections.iter_mut() {
            s.name = Some(shstr.lookup_str(s.header.sh_name as usize));
            // s.late_init(&mut sections, endian); TODO BLAH

            if s.header.sh_type == SHT_SYMTAB {
                s.init_symbols(&sections_before, endian);
            } else if s.is_rel() {
                relocated_bys.push((s.header.sh_info, s.index));

                s.rel_target = Some(sections_before[s.header.sh_info as usize].index);
                s.init_relocs(endian);
            }
        }

        for (target, reloc) in relocated_bys {
            let s = sections.get_mut(target as usize).unwrap();
            s.relocated_by.push(reloc);
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

    pub fn symtab_mut(&mut self) -> &mut Section {
        self.sections.get_mut(self.symtab.unwrap()).unwrap()
    }

    pub fn add_section(
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

        self.sections.last().unwrap()
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
                writer.write_all(&[0]).unwrap();
            }
        }
    }

    pub fn write(&mut self, filename: PathBuf) -> BinResult<()> {
        let mut file = std::fs::File::create(filename).unwrap();
        let mut writer = BufWriter::new(&mut file);

        self.header.e_shnum = self.sections.len() as u16;
        writer
            .write_all(&self.header.to_bin(self.endian).unwrap())
            .unwrap();

        for s in &mut self.sections {
            if s.header.sh_type != SHT_NOBITS && s.header.sh_type != SHT_NULL {
                Self::pad_out(&mut writer, s.header.sh_addralign as usize);
                let old_offset = s.header.sh_offset;
                s.header.sh_offset = writer.stream_position().unwrap() as u32;
                if s.header.sh_type == SHT_MIPS_DEBUG && s.header.sh_offset != old_offset {
                    // The .mdebug section has moved, relocate offsets
                    s.relocate_mdebug(old_offset as usize, self.endian)?;
                }
                writer.write_all(&s.data).unwrap();
            }
        }

        Self::pad_out(&mut writer, 4);
        self.header.e_shoff = writer.stream_position().unwrap() as u32;

        for s in &mut self.sections {
            writer
                .write_all(&s.header_to_bin(self.endian).unwrap())
                .unwrap();
        }

        writer.seek(SeekFrom::Start(0)).unwrap();
        writer
            .write_all(&self.header.to_bin(self.endian).unwrap())
            .unwrap();
        writer.flush().unwrap();
        Ok(())
    }

    pub fn fixup_objfile(
        objfile_path: &PathBuf,
        functions: &[Function],
        asm_prelude: &str,
        assembler: &str,
        output_enc: &str,
        drop_mdebug_gptab: bool,
        convert_statics: SymbolVisibility,
    ) -> Result<()> {
        const SECTIONS: [&str; 4] = [".data", ".text", ".rodata", ".bss"];

        let objfile_data = fs::read(objfile_path)?;
        let mut objfile = ElfFile::new(&objfile_data)?;
        let endian = objfile.endian;

        let mut prev_locs =
            HashMap::from([(".text", 0), (".data", 0), (".rodata", 0), (".bss", 0)]);

        let mut to_copy: HashMap<&str, Vec<ToCopyData>> = HashMap::from([
            (".text", vec![]),
            (".data", vec![]),
            (".rodata", vec![]),
            (".bss", vec![]),
        ]);

        let mut asm: Vec<String> = vec![];
        let mut all_late_rodata_dummy_bytes: Vec<Vec<[u8; 4]>> = vec![];
        let mut all_jtbl_rodata_size: Vec<usize> = vec![];
        let mut late_rodata_asm: Vec<String> = vec![];
        let mut late_rodata_source_name_start: Option<String> = None;
        let mut late_rodata_source_name_end: Option<String> = None;

        // Generate an assembly file with all the assembly we need to fill in. For
        // simplicity we pad with nops/.space so that addresses match exactly, so we
        // don't have to fix up relocations/symbol references.
        let mut all_text_glabels: HashSet<String> = HashSet::new();
        let mut func_sizes: HashMap<String, usize> = HashMap::new();

        for function in functions.iter() {
            let mut ifdefed = false;
            for (sectype, (temp_name, size)) in function.data.iter() {
                if temp_name.is_none() {
                    continue;
                }
                let temp_name = temp_name.as_ref().unwrap();
                if *size == 0 {
                    return Err(anyhow::anyhow!("Size of section {} is 0", temp_name));
                }
                let loc = objfile.symtab().find_symbol(temp_name);
                if loc.is_none() {
                    ifdefed = true;
                    break;
                }
                let loc = loc.unwrap().1;
                let prev_loc = prev_locs.get(sectype.as_str()).unwrap();
                if loc < *prev_loc {
                    // If the dummy C generates too little asm, and we have two
                    // consecutive GLOBAL_ASM blocks, we detect that error here.
                    // On the other hand, if it generates too much, we don't have
                    // a good way of discovering that error: it's indistinguishable
                    // from a static symbol occurring after the GLOBAL_ASM block.
                    return Err(anyhow::anyhow!(format!(
                    "Wrongly computed size for section {} (diff {}). This is an asm-processor bug!",
                    sectype,
                    prev_loc - loc
                )));
                }
                if loc != *prev_loc {
                    asm.push(format!(".section {}", sectype));
                    if sectype == ".text" {
                        for _ in 0..((loc - *prev_loc) / 4) {
                            asm.push("nop".to_owned());
                        }
                    } else {
                        asm.push(format!(".space {}", loc - *prev_loc));
                    }
                }
                to_copy.get_mut(sectype.as_str()).unwrap().push(ToCopyData {
                    loc,
                    size: *size,
                    temp_name: temp_name.to_string(),
                    fn_desc: function.fn_desc.clone(),
                });
                if !function.text_glabels.is_empty() && sectype == ".text" {
                    func_sizes.insert(function.text_glabels.first().unwrap().to_string(), *size);
                }
                prev_locs
                    .get_mut(sectype.as_str())
                    .map(|s| *s = loc + *size as u32);
            }

            if !ifdefed {
                all_text_glabels.extend(function.text_glabels.iter().cloned());
                all_late_rodata_dummy_bytes.push(function.late_rodata_dummy_bytes.clone());
                all_jtbl_rodata_size.push(function.jtbl_rodata_size);
                late_rodata_asm.extend(function.late_rodata_asm_conts.iter().cloned());
                for (sectype, (temp_name, _)) in function.data.iter() {
                    if temp_name.is_some() {
                        asm.push(format!(".section {}", sectype));
                        asm.push(format!("glabel {}_asm_start", temp_name.as_ref().unwrap()));
                    }
                }
                asm.push(".text".to_owned());
                asm.extend(function.asm_conts.iter().cloned());
                for (sectype, (temp_name, _)) in function.data.iter() {
                    if temp_name.is_some() {
                        asm.push(format!(".section {}", sectype));
                        asm.push(format!("glabel {}_asm_end", temp_name.as_ref().unwrap()));
                    }
                }
            }
        }

        if !late_rodata_asm.is_empty() {
            late_rodata_source_name_start = Some("_asmpp_late_rodata_start".to_string());
            late_rodata_source_name_end = Some("_asmpp_late_rodata_end".to_string());
            asm.push(".section .late_rodata".to_string());
            // Put some padding at the start to avoid conflating symbols with
            // references to the whole section.
            asm.push(".word 0, 0".to_string());
            asm.push(format!(
                "glabel {}",
                late_rodata_source_name_start.as_ref().unwrap()
            ));
            asm.extend(late_rodata_asm.iter().cloned());
            asm.push(format!(
                "glabel {}",
                late_rodata_source_name_end.as_ref().unwrap()
            ));
        }

        let temp_dir = TempDir::with_prefix("asm_processor")?;

        let obj_stem = objfile_path.file_stem().unwrap().to_str().unwrap();

        let o_file_path = temp_dir
            .path()
            .join(format!("asm_processor_{}.o", obj_stem));
        let mut o_file = File::create(&o_file_path)?;
        o_file.flush()?;

        let s_file_path = temp_dir
            .path()
            .join(format!("asm_processor_{}.s", obj_stem));
        let mut s_file = File::create(&s_file_path)?;
        s_file.write_all(asm_prelude.as_bytes())?;
        s_file.write_all("\n".as_bytes())?;

        let encoding = match encoding_rs::Encoding::for_label(output_enc.as_bytes()) {
            Some(encoding) => encoding,
            None => return Err(anyhow::anyhow!("Unsupported encoding: {}", output_enc)),
        };

        for line in asm {
            let line = encoding.encode(&line).0;
            s_file.write_all(&line)?;
            s_file.write_all("\n".as_bytes())?;
        }
        s_file.flush()?;

        let status = Command::new("sh")
            .arg("-c")
            .arg(format!(
                "{} {} -o {}",
                assembler,
                s_file_path.display(),
                o_file_path.display()
            ))
            .status()
            .expect("Failed to run assembler");
        if !status.success() {
            return Err(anyhow::anyhow!("Failed to assemble"));
        }
        let asm_objfile = ElfFile::new(&fs::read(&o_file_path)?)?;

        // Remove clutter from objdump output for tests, and make the tests
        // portable by avoiding absolute paths. Outside of tests .mdebug is
        // useful for showing source together with asm, though.
        let mdebug_section = objfile.find_section(".mdebug").cloned();
        if drop_mdebug_gptab {
            objfile.drop_mdebug_gptab();
        }

        // Unify reginfo sections
        let mut target_reginfo = objfile.find_section_mut(".reginfo");
        if target_reginfo.is_some() {
            let source_reginfo_data = asm_objfile.find_section(".reginfo").unwrap().data.clone();
            let mut data = target_reginfo.as_ref().unwrap().data.clone();
            for i in 0..20 {
                data[i] |= source_reginfo_data[i];
            }
            target_reginfo.as_mut().unwrap().data = data;
        }

        // Move over section contents
        let mut modified_text_positions = HashSet::new();
        let mut jtbl_rodata_positions: HashSet<usize> = HashSet::new();
        let mut last_rodata_pos = 0;
        for sectype in SECTIONS {
            if !to_copy.contains_key(sectype) || to_copy.get(sectype).unwrap().is_empty() {
                continue;
            }
            let source = asm_objfile.find_section(sectype);
            assert!(source.is_some());
            let source = source.unwrap();
            for to_copy_data in to_copy.get_mut(sectype).unwrap() {
                let loc1 = asm_objfile
                    .symtab()
                    .find_symbol_in_section(
                        &format!("{}_asm_start", &to_copy_data.temp_name),
                        source,
                    )
                    .unwrap();
                let loc2 = asm_objfile
                    .symtab()
                    .find_symbol_in_section(&format!("{}_asm_end", &to_copy_data.temp_name), source)
                    .unwrap();
                assert_eq!(loc1, to_copy_data.loc);
                if loc2 - loc1 != to_copy_data.size as u32 {
                    return Err(anyhow::anyhow!(
                    "incorrectly computed size for section {}, {}. If using .double, make sure to provide explicit alignment padding.",
                    sectype,
                    to_copy_data.fn_desc
                ));
                }
            }

            if sectype == ".bss" {
                continue;
            }

            let mut target = objfile.find_section_mut(sectype);
            assert!(target.is_some());
            let mut data = target.as_ref().unwrap().data.clone();
            for a in to_copy.get(sectype).unwrap().iter() {
                let pos = a.loc as usize;
                let count = a.size;

                data[pos..pos + count].copy_from_slice(&source.data[pos..pos + count]);

                if sectype == ".text" {
                    assert_eq!(a.size % 4, 0);
                    assert_eq!(a.loc % 4, 0);
                    for j in 0..a.size / 4 {
                        modified_text_positions.insert(a.loc as usize + 4 * j);
                    }
                } else if sectype == ".rodata" {
                    last_rodata_pos = a.loc as usize + a.size;
                }
            }
            target.as_mut().unwrap().data = data;
        }

        // Move over late rodata. This is heuristic, sadly, since I can't think
        // of another way of doing it.
        let mut moved_late_rodata: HashMap<u32, u32> = HashMap::new();
        if (!all_late_rodata_dummy_bytes.is_empty()
            && all_late_rodata_dummy_bytes.iter().any(|b| !b.is_empty()))
            || (!all_jtbl_rodata_size.is_empty() && all_jtbl_rodata_size.iter().any(|&s| s > 0))
        {
            let source = asm_objfile.find_section(".late_rodata").unwrap();
            let target = objfile.find_section_mut(".rodata").unwrap();
            let mut source_pos = asm_objfile
                .symtab()
                .find_symbol_in_section(late_rodata_source_name_start.unwrap().as_str(), source)
                .unwrap();
            let source_end = asm_objfile
                .symtab()
                .find_symbol_in_section(late_rodata_source_name_end.unwrap().as_str(), source)
                .unwrap();
            let mut expected_size: usize =
                all_late_rodata_dummy_bytes.iter().map(|x| x.len()).sum();
            expected_size *= 4;
            expected_size += all_jtbl_rodata_size.iter().sum::<usize>();

            if source_end - source_pos != expected_size as u32 {
                return Err(anyhow::anyhow!("computed wrong size of .late_rodata"));
            }
            let mut new_data = target.data.clone();

            for (dummy_bytes_list, jtbl_rodata_size) in all_late_rodata_dummy_bytes
                .iter_mut()
                .zip(all_jtbl_rodata_size.iter())
            {
                let dummy_bytes_list_len = dummy_bytes_list.len();

                for (index, dummy_bytes) in dummy_bytes_list.iter_mut().enumerate() {
                    let dummy_bytes = match endian {
                        Endian::Big => dummy_bytes,
                        Endian::Little => {
                            dummy_bytes.reverse();
                            dummy_bytes
                        }
                    };

                    let mut pos = target.data[last_rodata_pos..]
                        .windows(4)
                        .position(|x| x == dummy_bytes)
                        .unwrap()
                        + last_rodata_pos;

                    if index == 0
                        && dummy_bytes_list_len > 1
                        && target.data[pos + 4..pos + 8] == *b"\0\0\0\0"
                    {
                        // Ugly hack to handle double alignment for non-matching builds.
                        // We were told by .late_rodata_alignment (or deduced from a .double)
                        // that a function's late_rodata started out 4 (mod 8), and emitted
                        // a float and then a double. But it was actually 0 (mod 8), so our
                        // double was moved by 4 bytes. To make them adjacent to keep jump
                        // tables correct, move the float by 4 bytes as well.
                        new_data[pos..pos + 4].copy_from_slice(b"\0\0\0\0");
                        pos += 4;
                    }
                    new_data[pos..pos + 4].copy_from_slice(
                        source.data[source_pos as usize..source_pos as usize + 4].as_ref(),
                    );
                    moved_late_rodata.insert(source_pos, pos as u32);
                    last_rodata_pos = pos + 4;
                    source_pos += 4;
                }

                if *jtbl_rodata_size > 0 {
                    assert!(!dummy_bytes_list.is_empty());
                    let pos = last_rodata_pos;
                    new_data[pos..pos + jtbl_rodata_size].copy_from_slice(
                        source.data[source_pos as usize..source_pos as usize + jtbl_rodata_size]
                            .as_ref(),
                    );
                    for i in (0..*jtbl_rodata_size).step_by(4) {
                        moved_late_rodata.insert(source_pos + i as u32, (pos + i) as u32);
                        jtbl_rodata_positions.insert(pos + i);
                    }
                    last_rodata_pos += jtbl_rodata_size;
                    source_pos += *jtbl_rodata_size as u32;
                }
            }
            target.data = new_data;
        }

        // Merge strtab data.
        let strtab_adj = {
            let idx = objfile.symtab().strtab.unwrap();
            let strtab = objfile.sections.get_mut(idx).unwrap();

            let strtab_adj = strtab.data.len();
            strtab.data.extend(
                asm_objfile.sections[asm_objfile.symtab().strtab.unwrap()]
                    .data
                    .iter()
                    .cloned(),
            );

            strtab_adj
        };

        // Find relocated symbols
        let mut relocated_symbols = vec![];
        for sectype in SECTIONS.iter().chain([".late_rodata"].iter()) {
            // objfile
            if let Some(sec) = objfile.find_section(sectype) {
                for reltab_idx in &sec.relocated_by {
                    let reltab = &objfile.sections[*reltab_idx];
                    for rel in &reltab.relocations {
                        relocated_symbols.push(
                            objfile
                                .symtab()
                                .symbol_entries
                                .get(rel.sym_index())
                                .unwrap()
                                .clone(),
                        );
                    }
                }
            }

            // asm_objfile
            if let Some(sec) = asm_objfile.find_section(sectype) {
                for reltab_idx in &sec.relocated_by {
                    let reltab = &asm_objfile.sections[*reltab_idx];
                    for rel in &reltab.relocations {
                        relocated_symbols.push(
                            asm_objfile
                                .symtab()
                                .symbol_entries
                                .get(rel.sym_index())
                                .unwrap()
                                .clone(),
                        );
                    }
                }
            }
        }

        // Move over symbols, deleting the temporary function labels.
        // Skip over new local symbols that aren't relocated against, to
        // avoid conflicts.
        let empty_symbol = &objfile.symtab().symbol_entries[0].clone();
        let mut new_syms: Vec<Rc<RefCell<Symbol>>> = objfile
            .symtab()
            .symbol_entries
            .iter()
            .skip(1)
            .filter(|x| !x.borrow().name.starts_with("_asmpp_"))
            .cloned()
            .collect();

        for (i, s) in asm_objfile.symtab().symbol_entries.iter().enumerate() {
            let is_local = i < asm_objfile.symtab().header.sh_info as usize;
            if is_local && !relocated_symbols.contains(s) {
                continue;
            }
            if s.borrow().name.starts_with("_asmpp_") {
                assert!(!relocated_symbols.contains(s));
                continue;
            }
            if s.borrow().data.st_shndx != SHN_UNDEF && s.borrow().data.st_shndx != SHN_ABS {
                let section_name = asm_objfile.sections[s.borrow().data.st_shndx as usize]
                    .name
                    .clone()
                    .unwrap();
                let mut target_section_name = section_name.clone();
                if section_name == ".late_rodata" {
                    target_section_name = ".rodata".to_string();
                } else if !SECTIONS.contains(&section_name.as_str()) {
                    return Err(anyhow::anyhow!("generated assembly .o must only have symbols for .text, .data, .rodata, .late_rodata, ABS and UNDEF, but found {}", section_name));
                }
                let objfile_section = objfile.find_section(&target_section_name);
                if objfile_section.is_none() {
                    return Err(anyhow::anyhow!(
                        "generated assembly .o has section that real objfile lacks: {}",
                        target_section_name
                    ));
                }
                s.borrow_mut().data.st_shndx = objfile_section.unwrap().index as u16;
                // glabels aren't marked as functions, making objdump output confusing. Fix that.
                if all_text_glabels.contains(s.borrow().name.as_str()) {
                    s.borrow_mut().set_type(STT_FUNC);
                    if func_sizes.contains_key(s.borrow().name.as_str()) {
                        let siz: u32 = func_sizes[s.borrow().name.as_str()] as u32;
                        s.borrow_mut().data.st_size = siz;
                    }
                }
                if section_name == ".late_rodata" {
                    if s.borrow().data.st_value == 0 {
                        // This must be a symbol corresponding to the whole .late_rodata
                        // section, being referred to from a relocation.
                        // Moving local symbols is tricky, because it requires fixing up
                        // lo16/hi16 relocation references to .late_rodata+<offset>.
                        // Just disallow it for now.
                        return Err(anyhow::anyhow!(
                            "local symbols in .late_rodata are not allowed"
                        ));
                    }
                    let st_val = s.borrow().data.st_value;
                    s.borrow_mut().data.st_value = moved_late_rodata[&st_val];
                }
            }
            s.borrow_mut().data.st_name += strtab_adj as u32;
            new_syms.push(s.clone());
        }

        let make_statics_global = match convert_statics {
            SymbolVisibility::No => false,
            SymbolVisibility::Local => false,
            SymbolVisibility::Global => true,
            SymbolVisibility::GlobalWithFilename => true,
        };

        // Add static symbols from .mdebug, so they can be referred to from GLOBAL_ASM
        if mdebug_section.is_some() && convert_statics != SymbolVisibility::No {
            let mdebug_section = mdebug_section.unwrap();
            let mut static_name_count = HashMap::new();
            let mut strtab_index = objfile.sections[objfile.symtab().strtab.unwrap()]
                .data
                .len();
            let mut new_strtab_data = vec![];

            let ifd_max = u32::from_be_bytes(mdebug_section.data[18 * 4..19 * 4].try_into()?);
            let cb_fd_offset = u32::from_be_bytes(mdebug_section.data[19 * 4..20 * 4].try_into()?);
            let cb_sym_offset = u32::from_be_bytes(mdebug_section.data[9 * 4..10 * 4].try_into()?);
            let cb_ss_offset = u32::from_be_bytes(mdebug_section.data[15 * 4..16 * 4].try_into()?);

            for i in 0..ifd_max {
                let offset = cb_fd_offset + 18 * 4 * i;
                let iss_base = u32::from_be_bytes(
                    objfile.data[(offset + 2 * 4) as usize..(offset + 3 * 4) as usize]
                        .try_into()?,
                );
                let isym_base = u32::from_be_bytes(
                    objfile.data[(offset + 4 * 4) as usize..(offset + 5 * 4) as usize]
                        .try_into()?,
                );
                let csym = u32::from_be_bytes(
                    objfile.data[(offset + 5 * 4) as usize..(offset + 6 * 4) as usize]
                        .try_into()?,
                );
                let mut scope_level = 0;

                for j in 0..csym {
                    let offset2 = cb_sym_offset + 12 * (isym_base + j);
                    let iss = u32::from_be_bytes(
                        objfile.data[offset2 as usize..(offset2 + 4) as usize].try_into()?,
                    );
                    let value = u32::from_be_bytes(
                        objfile.data[(offset2 + 4) as usize..(offset2 + 8) as usize].try_into()?,
                    );
                    let st_sc_index = u32::from_be_bytes(
                        objfile.data[(offset2 + 8) as usize..(offset2 + 12) as usize].try_into()?,
                    );
                    let st = st_sc_index >> 26;
                    let sc = (st_sc_index >> 21) & 0x1F;

                    if st == MIPS_DEBUG_ST_STATIC || st == MIPS_DEBUG_ST_STATIC_PROC {
                        let symbol_name_offset = cb_ss_offset + iss_base + iss;
                        let symbol_name_offset_end = objfile_data
                            .iter()
                            .skip(symbol_name_offset as usize)
                            .position(|x| *x == 0)
                            .unwrap()
                            + symbol_name_offset as usize;
                        let mut symbol_name = String::from_utf8_lossy(
                            &objfile_data[symbol_name_offset as usize..symbol_name_offset_end],
                        )
                        .into_owned();
                        if scope_level > 1 {
                            // For in-function statics, append an increasing counter to
                            // the name, to avoid duplicate conflicting symbols.
                            let count =
                                static_name_count.get(symbol_name.as_str()).unwrap_or(&0) + 1;
                            static_name_count.insert(symbol_name.clone(), count);
                            symbol_name = format!("{}:{}", symbol_name, count);
                        }
                        let emitted_symbol_name =
                            if convert_statics == SymbolVisibility::GlobalWithFilename {
                                // Change the emitted symbol name to include the filename,
                                // but don't let that affect deduplication logic (we still
                                // want to be able to reference statics from GLOBAL_ASM).
                                format!("{}:{}", objfile_path.to_string_lossy(), symbol_name)
                            } else {
                                symbol_name.clone()
                            };
                        let section_name = match sc {
                            1 => ".text",
                            2 => ".data",
                            3 => ".bss",
                            15 => ".rodata",
                            _ => {
                                return Err(anyhow::anyhow!(
                                    "unsupported MIPS_DEBUG_SC value: {}",
                                    sc
                                ));
                            }
                        };
                        let section = objfile.find_section(section_name);
                        let symtype = if sc == 1 { STT_FUNC } else { STT_OBJECT };
                        let binding = if make_statics_global {
                            STB_GLOBAL
                        } else {
                            STB_LOCAL
                        };
                        let sym = Symbol::from_parts(
                            SymbolData {
                                st_name: strtab_index as u32,
                                st_value: value,
                                st_size: 0,
                                st_info: ((binding as u32) << 4 | symtype as u32) as u8,
                                st_other: STV_DEFAULT,
                                st_shndx: section.unwrap().index as u16,
                            },
                            symbol_name.as_str(),
                            endian,
                        )?;
                        strtab_index += emitted_symbol_name.len() + 1;
                        new_strtab_data.push(emitted_symbol_name + "\0");
                        new_syms.push(Rc::new(RefCell::new(sym)));
                    }
                    match st {
                        MIPS_DEBUG_ST_FILE
                        | MIPS_DEBUG_ST_STRUCT
                        | MIPS_DEBUG_ST_UNION
                        | MIPS_DEBUG_ST_ENUM
                        | MIPS_DEBUG_ST_BLOCK
                        | MIPS_DEBUG_ST_PROC
                        | MIPS_DEBUG_ST_STATIC_PROC => {
                            scope_level += 1;
                        }
                        MIPS_DEBUG_ST_END => {
                            scope_level -= 1;
                        }
                        _ => {}
                    }
                }
                assert_eq!(scope_level, 0);
            }

            {
                let idx = objfile.symtab().strtab.unwrap();
                let strtab = objfile.sections.get_mut(idx).unwrap();

                strtab.data.extend(new_strtab_data.join("").as_bytes());
            }
        }

        // Get rid of duplicate symbols, favoring ones that are not UNDEF.
        // Skip this for unnamed local symbols though.
        new_syms.sort_by(|a, b| {
            if a.borrow().data.st_shndx != SHN_UNDEF && b.borrow().data.st_shndx == SHN_UNDEF {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        });
        let mut old_syms: Vec<(Rc<RefCell<Symbol>>, Rc<RefCell<Symbol>>)> = vec![];
        let mut newer_syms = vec![];
        let mut name_to_sym = HashMap::new();
        for s in new_syms.iter_mut() {
            if s.borrow().name == "_gp_disp" {
                s.borrow_mut().set_type(STT_OBJECT);
            }
            if s.borrow().bind == STB_LOCAL && s.borrow().data.st_shndx == SHN_UNDEF {
                return Err(anyhow::anyhow!(
                    "local symbol \"{}\" is undefined",
                    s.borrow().name
                ));
            }
            if s.borrow().name.is_empty() {
                if s.borrow().bind != STB_LOCAL {
                    return Err(anyhow::anyhow!("global symbol with no name"));
                }
                newer_syms.push(s.clone());
            } else {
                let existing = name_to_sym.get(&s.borrow().name);
                if existing.is_none() {
                    name_to_sym.insert(s.borrow().name.clone(), s.clone());
                    newer_syms.push(s.clone());
                } else {
                    let existing = existing.unwrap();
                    if s.borrow().data.st_shndx != SHN_UNDEF
                        && !(existing.borrow().data.st_shndx == s.borrow().data.st_shndx
                            && existing.borrow().data.st_value == s.borrow().data.st_value)
                    {
                        return Err(anyhow::anyhow!(
                            "symbol \"{}\" defined twice",
                            s.borrow().name
                        ));
                    } else {
                        old_syms.push((s.clone(), existing.clone()));
                    }
                }
            }
        }
        new_syms = newer_syms;

        // Put local symbols in front, with the initial dummy entry first, and
        // _gp_disp at the end if it exists.
        new_syms.insert(0, empty_symbol.clone());
        new_syms.sort_by_key(|a| (a.borrow().bind != STB_LOCAL, a.borrow().name == "_gp_disp"));

        let num_local_syms = new_syms
            .iter()
            .filter(|x| x.borrow().bind == STB_LOCAL)
            .count();
        let new_sym_data: Vec<u8> = new_syms.iter().flat_map(|s| s.borrow().to_bin()).collect();
        let mut new_index = HashMap::new();

        for (i, s) in new_syms.iter().enumerate() {
            new_index.insert(s.borrow().name.clone(), i);
        }
        for (s, replace_by) in old_syms.iter() {
            new_index.insert(
                s.borrow().name.clone(),
                new_index[&replace_by.borrow().name],
            );
        }

        objfile.symtab_mut().data = new_sym_data;
        objfile.symtab_mut().header.sh_info = num_local_syms as u32;

        // Fix up relocation symbol references
        for sectype in SECTIONS {
            let target = objfile.find_section(sectype).cloned();

            if let Some(target) = target {
                let symbol_entries = objfile.symtab().symbol_entries.clone();

                // fixup relocation symbol indices, since we butchered them above
                for reltab in target.relocated_by.iter() {
                    let reltab = &mut objfile.sections[*reltab];
                    let mut nrels = vec![];
                    for rel in reltab.relocations.iter() {
                        let mut rel = rel.clone();
                        if sectype == ".text"
                            && modified_text_positions.contains(&(rel.data.inner.r_offset as usize))
                            || sectype == ".rodata"
                                && jtbl_rodata_positions
                                    .contains(&(rel.data.inner.r_offset as usize))
                        {
                            // don't include relocations for late_rodata dummy code
                            continue;
                        }
                        rel.set_sym_index(
                            new_index[&symbol_entries[rel.sym_index()].borrow().name],
                        );
                        nrels.push(rel.clone());
                    }
                    reltab.data = nrels
                        .iter()
                        .flat_map(|x| x.to_bin(endian).unwrap())
                        .collect();
                    reltab.relocations = nrels;
                }
            }
        }

        // Move over relocations
        for sectype in SECTIONS.iter().chain([".late_rodata"].iter()) {
            if let Some(source) = asm_objfile.find_section(sectype) {
                if source.data.is_empty() {
                    continue;
                }

                let target_sectype = if *sectype == ".late_rodata" {
                    ".rodata"
                } else {
                    sectype
                };
                let target_index = objfile.find_section(target_sectype).unwrap().index as u32;
                for reltab in &source.relocated_by {
                    let reltab = &mut asm_objfile.sections[*reltab].clone();
                    for rel in &mut reltab.relocations {
                        rel.set_sym_index(
                            new_index[&asm_objfile.symtab().symbol_entries[rel.sym_index()]
                                .borrow()
                                .name],
                        );
                        if *sectype == ".late_rodata" {
                            rel.data.inner.r_offset = moved_late_rodata[&(rel.data.inner.r_offset)];
                        }
                    }
                    let new_data: Vec<u8> = reltab
                        .relocations
                        .iter()
                        .flat_map(|x| x.to_bin(endian).unwrap())
                        .collect();

                    if reltab.header.sh_type == SHT_REL {
                        if let Some(target_reltab) =
                            objfile.find_section_mut(format!(".rel{}", target_sectype).as_str())
                        {
                            target_reltab.data.extend(new_data);
                        } else {
                            objfile.add_section(
                                format!("rel{}", target_sectype).as_str(),
                                SHT_REL,
                                0,
                                objfile.symtab().index as u32,
                                target_index,
                                4,
                                8,
                                &new_data,
                                endian,
                            );
                        }
                    } else if let Some(target_reltaba) =
                        objfile.find_section_mut(format!(".rela{}", target_sectype).as_str())
                    {
                        target_reltaba.data.extend(new_data);
                    } else {
                        objfile.add_section(
                            format!("rel{}", target_sectype).as_str(),
                            SHT_REL,
                            0,
                            objfile.symtab().index as u32,
                            target_index,
                            4,
                            8,
                            &new_data,
                            endian,
                        );
                    }
                }
            }
        }
        objfile.write(objfile_path.to_path_buf())?;

        fs::remove_file(s_file_path)?;
        fs::remove_file(o_file_path)?;
        Ok(())
    }
}
