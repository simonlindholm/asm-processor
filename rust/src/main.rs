mod asm;
mod elf;

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    fs::{self, read_to_string, File},
    hash::Hash,
    io::{stdout, Write},
    ops::Index,
    path::{Path, PathBuf},
    process::Command,
    thread::scope,
};

use anyhow::{Context, Result};
use asm::GlobalAsmBlock;
use binrw::Endian;
use clap::{Args, Parser, ValueEnum};
use elf::{ElfFile, Symbol};
use encoding_rs::Encoding;
use regex::Regex;
use temp_dir::TempDir;

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

const MIPS_DEBUG_ST_STATIC: u32 = 2;
const MIPS_DEBUG_ST_PROC: u32 = 6;
const MIPS_DEBUG_ST_BLOCK: u32 = 7;
const MIPS_DEBUG_ST_END: u32 = 8;
const MIPS_DEBUG_ST_FILE: u32 = 11;
const MIPS_DEBUG_ST_STATIC_PROC: u32 = 14;
const MIPS_DEBUG_ST_STRUCT: u32 = 26;
const MIPS_DEBUG_ST_UNION: u32 = 27;
const MIPS_DEBUG_ST_ENUM: u32 = 28;

#[derive(Clone, Debug)]
struct GlobalState {
    late_rodata_hex: u32,
    valuectr: usize,
    namectr: usize,
    min_instr_count: usize,
    skip_instr_count: usize,
    use_jtbl_for_rodata: bool,
    prelude_if_late_rodata: usize,
    mips1: bool,
    pascal: bool,
}

impl GlobalState {
    fn new(
        min_instr_count: usize,
        skip_instr_count: usize,
        use_jtbl_for_rodata: bool,
        prelude_if_late_rodata: usize,
        mips1: bool,
        pascal: bool,
    ) -> Self {
        Self {
            // A value that hopefully never appears as a 32-bit rodata constant (or we
            // miscompile late rodata). Increases by 1 in each step.
            late_rodata_hex: 0xE0123456,
            valuectr: 0,
            namectr: 0,
            min_instr_count: min_instr_count,
            skip_instr_count: skip_instr_count,
            use_jtbl_for_rodata: use_jtbl_for_rodata,
            prelude_if_late_rodata: prelude_if_late_rodata,
            mips1: mips1,
            pascal: pascal,
        }
    }

    fn next_late_rodata_hex(&mut self) -> [u8; 4] {
        let dummy_bytes = self.late_rodata_hex.to_be_bytes();
        if (self.late_rodata_hex & 0xffff) == 0 {
            // Avoid lui
            self.late_rodata_hex += 1;
        }
        self.late_rodata_hex += 1;
        dummy_bytes
    }

    fn make_name(&mut self, cat: &str) -> String {
        self.namectr += 1;
        format!("_asmpp_{}{}", cat, self.namectr)
    }

    fn func_prologue(&self, name: &str) -> String {
        if self.pascal {
            [
                format!("procedure {}();", name).as_str(),
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
            ]
            .join(" ")
        } else {
            format!("void {}(void) {{", name)
        }
    }

    fn func_epilogue(&self) -> String {
        if self.pascal {
            "end;".to_string()
        } else {
            "}".to_string()
        }
    }

    fn pascal_assignment_float(&mut self, tp: &str, val: f32) -> String {
        self.valuectr += 1;
        let address = (8 * self.valuectr) & 0x7FFF;
        format!("v{} := p{}({}); v{}^ := {};", tp, tp, address, tp, val)
    }

    fn pascal_assignment_double(&mut self, tp: &str, val: f64) -> String {
        self.valuectr += 1;
        let address = (8 * self.valuectr) & 0x7FFF;
        format!("v{} := p{}({}); v{}^ := {};", tp, tp, address, tp, val)
    }

    fn pascal_assignment_int(&mut self, tp: &str, val: i32) -> String {
        self.valuectr += 1;
        let address = (8 * self.valuectr) & 0x7FFF;
        format!("v{} := p{}({}); v{}^ := {};", tp, tp, address, tp, val)
    }
}

#[derive(Clone, Debug, Default, PartialEq, ValueEnum)]
enum SymbolVisibility {
    No,
    #[default]
    Local,
    Global,
    GlobalWithFilename,
}
#[derive(Args, Debug)]
#[group(required = false, multiple = false)]
struct OptFlag {
    #[clap(long = "O0", action)]
    o0: bool,

    #[clap(long = "O1", action)]
    o1: bool,

    #[clap(long = "O2", action)]
    o2: bool,

    #[clap(long = "O3", action)]
    g: bool,
}

#[derive(Clone, Debug, Default, PartialEq)]
enum OptLevel {
    #[default]
    O0,
    O1,
    O2,
    G,
}

#[derive(Clone, Debug, Parser)]
#[command(version, about, long_about = None)]
struct AsmProcArgs {
    /// path to .c code
    filename: PathBuf,

    /// path to .o file to post-process
    #[clap(required = false)]
    post_process: Option<PathBuf>,

    /// assembler command (e.g. "mips-linux-gnu-as -march=vr4300 -mabi=32")
    assembler: Option<String>,

    /// path to a file containing a prelude to the assembly file (with .set and .macro directives, e.g.)
    asm_prelude: Option<PathBuf>,

    /// input encoding
    #[clap(long, default_value = "latin1", required = false)]
    input_enc: String,

    /// output encoding
    #[clap(long, default_value = "latin1", required = false)]
    output_enc: String,

    /// drop mdebug and gptab sections
    #[clap(long, action)]
    drop_mdebug_gptab: bool,

    /// change static symbol visibility
    #[clap(long)]
    convert_statics: Option<SymbolVisibility>,

    /// force processing of files without GLOBAL_ASM blocks
    #[clap(long, action)]
    force: bool,

    /// Replace floats with their encoded hexadecimal representation in CutsceneData data
    #[clap(long, action)]
    enable_cutscene_data_float_encoding: bool,

    #[clap(long, action)]
    framepointer: bool,

    #[clap(long, action)]
    mips1: bool,

    #[clap(long, action)]
    g3: bool,

    #[clap(long = "KPIC", action)]
    kpic: bool,

    #[clap(skip)]
    opt: OptLevel,

    #[clap(skip)]
    pascal: bool,
}

#[derive(Clone, Debug)]
struct Function {
    text_glabels: Vec<String>,
    asm_conts: Vec<String>,
    late_rodata_dummy_bytes: Vec<[u8; 4]>,
    jtbl_rodata_size: usize,
    late_rodata_asm_conts: Vec<String>,
    fn_desc: String,
    data: HashMap<String, (Option<String>, usize)>,
}

/// Convert a float string to its hexadecimal representation
fn repl_float_hex(cap: &regex::Captures) -> String {
    let float_str = cap[0].trim().trim_end_matches('f');
    let float_val = float_str.parse::<f32>().unwrap();
    let hex_val = f32::to_be_bytes(float_val);
    format!("{}", u32::from_be_bytes(hex_val))
}

fn parse_source(infile_path: &Path, args: &AsmProcArgs, encode: bool) -> Result<RunResult> {
    let (mut min_instr_count, mut skip_instr_count) = match (args.opt.clone(), args.g3) {
        (OptLevel::O0, false) => match args.framepointer {
            true => (8, 8),
            false => (4, 4),
        },
        (OptLevel::O1, false) | (OptLevel::O2, false) => match args.framepointer {
            true => (6, 5),
            false => (2, 1),
        },
        (OptLevel::G, false) => match args.framepointer {
            true => (7, 7),
            false => (4, 4),
        },
        (OptLevel::O2, true) => match args.framepointer {
            true => (4, 4),
            false => (2, 2),
        },
        _ => {
            return Err(anyhow::anyhow!(
                "Unsupported optimization level: -g3 can only be used with -O2"
            ))
            .context("Invalid arguments")
        }
    };

    let mut prelude_if_late_rodata = 0;
    if args.kpic {
        // Without optimizations, the PIC prelude always takes up 3 instructions.
        // With optimizations, the prelude is optimized out if there's no late rodata.
        if args.opt == OptLevel::O2 || args.g3 {
            prelude_if_late_rodata = 3;
        } else {
            min_instr_count += 3;
            skip_instr_count += 3;
        }
    }

    let use_jtbl_for_rodata =
        (args.opt == OptLevel::O2 || args.g3) && !args.framepointer && !args.kpic;

    let mut state = GlobalState::new(
        min_instr_count,
        skip_instr_count,
        use_jtbl_for_rodata,
        prelude_if_late_rodata,
        args.mips1,
        args.pascal,
    );
    let output_enc = args.output_enc.clone();
    let mut global_asm: Option<GlobalAsmBlock> = None;
    let mut asm_functions: Vec<Function> = vec![];
    let mut output_lines: Vec<String> = vec![format!("\"#line 1 {} \"", infile_path.display())];
    let mut deps: Vec<String> = vec![];

    let mut is_cutscene_data = false;
    let mut is_early_include = false;
    let mut start_index: Option<usize> = None;

    let cutscene_re = Regex::new(r"CutsceneData (.|\n)*\[\] = {")?;

    for (line_no, line) in read_to_string(infile_path)?.lines().enumerate() {
        let mut raw_line = line.trim().to_owned();
        let line = raw_line.trim_start();

        // Print exactly one output line per source line, to make compiler
        // errors have correct line numbers. These will be overridden with
        // reasonable content further down.
        output_lines.push("".to_owned());

        if let Some(ref mut gasm) = global_asm {
            if line.starts_with(")") {
                let (src, fun) = gasm.finish(&mut state)?;
                for (i, line2) in src.iter().enumerate() {
                    output_lines[start_index.unwrap() + i] = line2.clone();
                }
                asm_functions.push(fun);
                global_asm = None;
            } else {
                gasm.process_line(&raw_line, &output_enc)?;
            }
        } else if line == "GLOBAL_ASM(" || line == "#pragma GLOBAL_ASM(" {
            global_asm = Some(GlobalAsmBlock::new(format!(
                "GLOBAL_ASM block at line {}",
                &line_no.to_string()
            )));
            start_index = Some(output_lines.len());
        } else if (line.starts_with("GLOBAL_ASM(\"") || line.starts_with("#pragma GLOBAL_ASM(\""))
            && line.ends_with("\")")
        {
            let fname = line[line.find("(").unwrap() + 2..line.len() - 2].to_string();
            deps.push(fname.clone());
            let mut gasm = GlobalAsmBlock::new(fname.clone());
            for line2 in read_to_string(fname)?.lines() {
                gasm.process_line(line2.trim_end(), &output_enc)?;
            }
            let (src, fun) = gasm.finish(&mut state)?;
            let output_lines_len = output_lines.len();
            output_lines[output_lines_len - 1] = src.join("");
            asm_functions.push(fun);
        } else if line == "#pragma asmproc recurse" {
            // C includes qualified as
            // #pragma asmproc recurse
            // #include "file.c"
            // will be processed recursively when encountered
            is_early_include = true;
        } else if is_early_include {
            // Previous line was a #pragma asmproc recurse
            is_early_include = false;
            if !line.starts_with("#include ") {
                return Err(anyhow::anyhow!(
                    "#pragma asmproc recurse must be followed by an #include "
                ));
            }
            let fpath = infile_path.parent().unwrap();
            let fname = fpath.join(line[line.find(' ').unwrap() + 2..].trim());
            deps.push(fname.to_str().unwrap().to_string());
            let mut res = parse_source(&fname, args, false)?;
            deps.append(&mut res.deps);
            let res_str = format!(
                "{}#line {} '{}'",
                res.output.clone(),
                line_no + 1,
                infile_path.file_name().unwrap().to_str().unwrap()
            );

            let output_lines_len = output_lines.len();
            output_lines[output_lines_len - 1] = res_str;
        } else {
            if args.enable_cutscene_data_float_encoding {
                // This is a hack to replace all floating-point numbers in an array of a particular type
                // (in this case CutsceneData) with their corresponding IEEE-754 hexadecimal representation
                if cutscene_re.is_match(line) {
                    is_cutscene_data = true;
                } else if line.ends_with("};") {
                    is_cutscene_data = false;
                }

                if is_cutscene_data {
                    raw_line = cutscene_re
                        .replace_all(&raw_line, repl_float_hex)
                        .into_owned();
                }
            }
            let output_lines_len = output_lines.len();
            output_lines[output_lines_len - 1] = raw_line.to_owned();
        }
    }

    let out_str = match encode {
        false => output_lines.join("\n"),
        true => {
            let newline_encoded = match Encoding::for_label(output_enc.as_bytes()) {
                Some(encoding) => encoding.encode("\n").0,
                None => return Err(anyhow::anyhow!("Unsupported encoding")),
            };

            let mut out_data = vec![];
            for line in output_lines {
                let line_encoded = match Encoding::for_label(output_enc.as_bytes()) {
                    Some(encoding) => encoding.encode(&line).0,
                    None => {
                        return Err(anyhow::anyhow!("Unsupported encoding"));
                    }
                };
                out_data.write_all(&line_encoded)?;
                out_data.write_all(&newline_encoded)?;
            }
            String::from_utf8(out_data)?
        }
    };

    Ok(RunResult {
        functions: asm_functions,
        deps,
        output: out_str,
    })
}

pub struct ToCopyData {
    loc: u32,
    size: usize,
    temp_name: String,
    fn_desc: String,
}

fn fixup_objfile(
    objfile_path: &PathBuf,
    functions: &[Function],
    asm_prelude: &str,
    assembler: &str,
    output_enc: &str,
    drop_mdebug_gptab: bool,
    convert_statics: SymbolVisibility,
) -> Result<()> {
    const SECTIONS: [&str; 4] = [".data", ".text", ".rodata", ".bss"];

    let mut objfile_data = fs::read(objfile_path)?;
    let mut objfile = ElfFile::new(&objfile_data)?;
    let endian = objfile.endian;

    let mut prev_locs = HashMap::from([(".text", 0), (".data", 0), (".rodata", 0), (".bss", 0)]);

    let mut to_copy: HashMap<&str, Vec<ToCopyData>> = HashMap::from([
        (".text", vec![]),
        (".data", vec![]),
        (".rodata", vec![]),
        (".bss", vec![]),
    ]);

    let mut asm: Vec<String> = vec![];
    let mut all_late_rodata_dummy_bytes: Vec<[u8; 4]> = vec![];
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
                func_sizes
                    .get_mut(function.text_glabels.first().unwrap())
                    .map(|s| {
                        *s = *size; // todo does this work and is this the best way to do this
                    });
            }
            prev_locs
                .get_mut(sectype.as_str())
                .map(|s| *s = loc + *size as u32);
        }

        if !ifdefed {
            all_text_glabels.extend(function.text_glabels.iter().cloned());
            all_late_rodata_dummy_bytes.extend(function.late_rodata_dummy_bytes.iter().cloned());
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

    let o_file_name = format!("asm_processor_{}.o", obj_stem);
    let s_file_name = format!("asm_processor_{}.s", obj_stem);

    let o_file_path = temp_dir.path().join(o_file_name);
    let mut o_file = File::create(&o_file_path)?;
    o_file.flush()?;

    let s_file_path = temp_dir.path().join(s_file_name);
    let mut s_file = File::create(&s_file_path)?;
    s_file.write_all(asm_prelude.as_bytes())?;
    s_file.write_all("\n".as_bytes())?;
    s_file.write_all(asm.join("\n").as_bytes())?;
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
    let mdebug_section = objfile.find_section(".mdebug");
    if drop_mdebug_gptab {
        objfile.drop_mdebug_gptab();
    }

    // Unify reginfo sections
    let mut target_reginfo = objfile.find_section_mut(".reginfo");
    if target_reginfo.is_some() {
        let source_reginfo_data = asm_objfile.find_section(".reginfo").unwrap().data.clone();
        let mut data = target_reginfo.as_ref().unwrap().data.clone();
        for i in 0..20 {
            if data[i] == 0 {
                data[i] |= source_reginfo_data[i];
            }
        }
        target_reginfo.as_mut().unwrap().data = data;
    }

    // Move over section contents
    let mut modified_text_positions = HashSet::new();
    let mut jtbl_rodata_positions: HashSet<usize> = HashSet::new();
    let mut last_rodata_pos = 0;
    for sectype in SECTIONS {
        if !to_copy.contains_key(sectype) {
            continue;
        }
        let source = asm_objfile.find_section(sectype);
        assert!(source.is_some());
        let source = source.unwrap();
        for to_copy_data in to_copy.get_mut(sectype).unwrap() {
            let loc1 = asm_objfile
                .symtab()
                .find_symbol_in_section(&format!("{}_asm_start", &to_copy_data.temp_name), source)
                .unwrap();
            let loc2 = asm_objfile
                .symtab()
                .find_symbol_in_section(&format!("{}_asm_end", &to_copy_data.temp_name), source)
                .unwrap();
            assert_eq!(loc1, to_copy_data.loc);
            if loc2 - loc1 != to_copy_data.size as u32 {
                return Err(anyhow::anyhow!(
                    "incorrectly computed size for section {}, {}. If using .double, make sure to provide explicit alignment padding.",
                    to_copy_data.temp_name,
                    loc2 - loc1
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
            let count = a.size as usize;

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
    if !all_late_rodata_dummy_bytes.is_empty() || !all_jtbl_rodata_size.is_empty() {
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
        let mut expected_size: usize = all_late_rodata_dummy_bytes.iter().map(|x| x.len()).sum();
        expected_size *= 4;
        expected_size += all_jtbl_rodata_size.iter().sum::<usize>();

        if source_end - source_pos != expected_size as u32 {
            return Err(anyhow::anyhow!("computed wrong size of .late_rodata"));
        }
        let mut new_data = target.data.clone();

        for (dummy_bytes_list, jtbl_rodata_size) in all_late_rodata_dummy_bytes
            .iter()
            .zip(all_jtbl_rodata_size.iter())
        {
            for (index, dummy_bytes) in dummy_bytes_list.iter().enumerate() {
                let dummy_bytes = match endian {
                    Endian::Big => dummy_bytes,
                    Endian::Little => {
                        let dummy_bytes = dummy_bytes.clone();
                        dummy_bytes.reverse_bits();
                        &dummy_bytes.to_owned()
                    }
                };
                // TODO eth this is definitely broken
                let mut pos = *target
                    .data
                    .iter()
                    .skip(last_rodata_pos)
                    .find(|x| *x == dummy_bytes)
                    .unwrap() as usize
                    + last_rodata_pos;

                if index == 0
                    && dummy_bytes_list.len() > 1
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
    // strtab_adj = len(objfile.symtab.strtab.data)
    // objfile.symtab.strtab.data += asm_objfile.symtab.strtab.data
    // TODO fix
    // let strtab = objfile
    //     .sections
    //     .get_mut(objfile.symtab().strtab.unwrap())
    //     .unwrap();
    // TODO eth this is wrong - we need something like the above but it breaks the borrow-checker
    let mut strtab = objfile.sections[0].clone();

    let strtab_adj = strtab.data.len();
    strtab.data.extend(
        asm_objfile.sections[objfile.symtab().strtab.unwrap()]
            .data
            .iter()
            .cloned(),
    );

    // Find relocated symbols
    let mut relocated_symbols = HashSet::new();
    for sectype in SECTIONS.iter().chain([".late_rodata"].iter()) {
        // objfile
        if let Some(sec) = objfile.find_section(&sectype) {
            for reltab_idx in &sec.relocated_by {
                let reltab = &objfile.sections[*reltab_idx];
                for rel in &reltab.relocations {
                    relocated_symbols.insert(
                        objfile
                            .symtab()
                            .symbol_entries
                            .get(rel.sym_index())
                            .unwrap(),
                    );
                }
            }
        }

        // asm_objfile
        if let Some(sec) = asm_objfile.find_section(&sectype) {
            for reltab_idx in &sec.relocated_by {
                let reltab = &asm_objfile.sections[*reltab_idx];
                for rel in &reltab.relocations {
                    relocated_symbols.insert(
                        asm_objfile
                            .symtab()
                            .symbol_entries
                            .get(rel.sym_index())
                            .unwrap(),
                    );
                }
            }
        }
    }

    // Move over symbols, deleting the temporary function labels.
    // Skip over new local symbols that aren't relocated against, to
    // avoid conflicts.
    let empty_symbol = &objfile.symtab().symbol_entries[0];
    let mut new_syms: Vec<Symbol> = objfile
        .symtab()
        .symbol_entries
        .iter()
        .skip(1)
        .filter(|x| !x.name.starts_with("_asmpp_"))
        .map(|x| x.clone())
        .collect();

    for (i, s) in asm_objfile.symtab().symbol_entries.iter().enumerate() {
        let mut s = s.clone();
        let is_local = i < asm_objfile.symtab().header.sh_info as usize;
        if is_local && !relocated_symbols.contains(&s) {
            continue;
        }
        if s.name.starts_with("_asmpp_") {
            assert!(!relocated_symbols.contains(&s));
            continue;
        }
        if s.data.st_shndx != SHN_UNDEF && s.data.st_shndx != SHN_UNDEF {
            let section_name = asm_objfile.sections[s.data.st_shndx as usize]
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
            s.data.st_shndx = objfile_section.unwrap().index as u16;
            // glabels aren't marked as functions, making objdump output confusing. Fix that.
            if all_text_glabels.contains(s.name.as_str()) {
                s.typ = STT_FUNC;
                if func_sizes.contains_key(s.name.as_str()) {
                    s.data.st_size = func_sizes[s.name.as_str()] as u32;
                }
            }
            if section_name == ".late_rodata" {
                if s.data.st_value == 0 {
                    // This must be a symbol corresponding to the whole .late_rodata
                    // section, being referred to from a relocation.
                    // Moving local symbols is tricky, because it requires fixing up
                    // lo16/hi16 relocation references to .late_rodata+<offset>.
                    // Just disallow it for now.
                    return Err(anyhow::anyhow!(
                        "local symbols in .late_rodata are not allowed"
                    ));
                }
                s.data.st_value = moved_late_rodata[&(s.data.st_value)];
            }
        }
        s.data.st_name += strtab_adj as u32;
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
        let mut static_name_count = HashMap::new();
        let mut strtab_index = objfile.sections[objfile.symtab().strtab.unwrap()]
            .data
            .len();
        let mut new_strtab_data = vec![];

        let ifd_max = u32::from_be_bytes(mdebug_section.unwrap().data[18 * 4..19 * 4].try_into()?);
        let cb_fd_offset =
            u32::from_be_bytes(mdebug_section.unwrap().data[19 * 4..20 * 4].try_into()?);
        let cb_sym_offset =
            u32::from_be_bytes(mdebug_section.unwrap().data[9 * 4..10 * 4].try_into()?);
        let cb_ss_offset =
            u32::from_be_bytes(mdebug_section.unwrap().data[15 * 4..16 * 4].try_into()?);

        for i in 0..ifd_max {
            let offset = cb_fd_offset + 18 * 4 * i;
            let iss_base = u32::from_be_bytes(
                objfile.data[(offset + 2 * 4) as usize..(offset + 3 * 4) as usize].try_into()?,
            );
            let isym_base = u32::from_be_bytes(
                objfile.data[(offset + 4 * 4) as usize..(offset + 5 * 4) as usize].try_into()?,
            );
            let csym = u32::from_be_bytes(
                objfile.data[(offset + 5 * 4) as usize..(offset + 6 * 4) as usize].try_into()?,
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
                        let count = static_name_count
                            .get(symbol_name.as_str())
                            .or(Some(&0))
                            .unwrap()
                            + 1;
                        static_name_count.insert(symbol_name.clone(), count);
                        symbol_name = format!("{}_{}", symbol_name, count);
                    }
                    let emitted_symbol_name =
                        if convert_statics == SymbolVisibility::GlobalWithFilename {
                            // Change the emitted symbol name to include the filename,
                            // but don't let that affect deduplication logic (we still
                            // want to be able to reference statics from GLOBAL_ASM).
                            format!(
                                "{}_{}",
                                objfile_path.file_stem().unwrap().to_str().unwrap(),
                                symbol_name
                            )
                        } else {
                            symbol_name.clone()
                        };
                    let section_name = match sc {
                        1 => ".text",
                        2 => ".data",
                        3 => ".bss",
                        15 => ".rodata",
                        _ => {
                            return Err(anyhow::anyhow!("unsupported MIPS_DEBUG_SC value: {}", sc));
                        }
                    };
                    let section = objfile.find_section(&section_name);
                    let symtype = if sc == 1 { STT_FUNC } else { STT_OBJECT };
                    let binding = if make_statics_global {
                        STB_GLOBAL
                    } else {
                        STB_LOCAL
                    };
                    let sym = Symbol::from_parts(
                        strtab_index as u32,
                        value,
                        0,
                        (binding << 4 | symtype as u32) as u8,
                        STV_DEFAULT,
                        section.unwrap().index as u16,
                        &strtab, //objfile.symtab().strtab.unwrap(),
                        symbol_name.as_str(),
                        endian,
                    )?;
                    strtab_index += emitted_symbol_name.len() + 1;
                    new_strtab_data.push(emitted_symbol_name + "\0");
                    new_syms.push(sym);
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
        strtab.data.extend(new_strtab_data.join("").as_bytes());
    }

    // Get rid of duplicate symbols, favoring ones that are not UNDEF.
    // Skip this for unnamed local symbols though.

    // TODO implement
    Ok(())
}

#[derive(Default)]
struct RunResult {
    functions: Vec<Function>,
    deps: Vec<String>,
    output: String,
}

fn run(
    args: &AsmProcArgs,
    mut outfile: impl Write,
    in_functions: Option<&[Function]>,
) -> Result<RunResult> {
    if args.post_process.is_none() {
        let res = parse_source(&args.filename, &args, false)?;
        outfile.write(res.output.as_bytes())?;
        return Ok(res);
    } else {
        let objfile = args.post_process.clone().unwrap();

        let assembler = args
            .assembler
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Assembler command is required when post-processing"))?;

        let functions = match in_functions {
            Some(funcs) => funcs.to_vec(),
            None => {
                let res = parse_source(&args.filename, &args, false)?;
                res.functions
            }
        };

        if (functions.is_empty()) && !args.force {
            return Ok(RunResult::default());
        }

        let asm_prelude = match &args.asm_prelude {
            Some(prelude) => fs::read_to_string(prelude)?,
            None => "".to_string(),
        };

        fixup_objfile(
            &objfile,
            &functions,
            &asm_prelude,
            assembler,
            &args.output_enc,
            args.drop_mdebug_gptab,
            args.convert_statics.clone().unwrap(),
        )?;
    }

    Ok(RunResult::default())
}

fn parse_args(args: &[String], compile_args: &[String]) -> Result<AsmProcArgs> {
    let mut args = AsmProcArgs::parse_from(args);

    if args.convert_statics.is_none() {
        args.convert_statics = Some(SymbolVisibility::Local);
    }

    if args.g3 && args.opt != OptLevel::O2 {
        Err(anyhow::anyhow!("-g3 is only supported together with -O2"))
            .context("Invalid arguments")?;
    }

    if args.mips1 && (!(args.opt == OptLevel::O1 || args.opt == OptLevel::O2) || args.framepointer)
    {
        Err(anyhow::anyhow!(
            "-mips1 is only supported together with -O1 or -O2"
        ))
        .context("Invalid arguments")?;
    }

    let is_pascal = args.filename.ends_with(".p")
        || args.filename.ends_with(".pas")
        || args.filename.ends_with(".pp");

    if is_pascal && !(args.opt == OptLevel::O1 || args.opt == OptLevel::O2 || args.g3) {
        Err(anyhow::anyhow!(
            "Pascal is only supported together with -O1, -O2 or -O2 -g3"
        ))
        .context("Invalid arguments")?;
    }

    args.pascal = is_pascal;

    for x in compile_args.iter().rev() {
        match x.as_str() {
            "-g" => {
                args.opt = OptLevel::G;
                break;
            }
            "-O0" => {
                args.opt = OptLevel::O0;
                break;
            }
            "-O1" => {
                args.opt = OptLevel::O1;
                break;
            }
            "-O2" => {
                args.opt = OptLevel::O2;
                break;
            }
            _ => {}
        }
    }

    if compile_args.contains(&"-mips1".to_string()) {
        args.mips1 = true;
    }
    if !compile_args.contains(&"-mips2".to_string()) {
        args.mips1 = true;
    }

    if compile_args.contains(&"-g3".to_string()) {
        args.g3 = true;
    }
    if compile_args.contains(&"-framepointer".to_string()) {
        args.framepointer = true;
    }
    if compile_args.contains(&"-KPIC".to_string()) {
        args.kpic = true;
    }

    Ok(args)
}

fn main() -> Result<()> {
    let os_args: Vec<String> = std::env::args().collect();

    let all_args = os_args[1..].to_vec();
    let sep0 = all_args
        .iter()
        .position(|arg| !arg.starts_with("-"))
        .expect("No first separator found");
    let sep1 = all_args
        .iter()
        .position(|arg| arg == "--")
        .expect("No first -- separator found");
    let offset = sep1 + 1;
    let sep2 = all_args[offset..]
        .iter()
        .position(|arg| arg == "--")
        .expect("No second -- separator found")
        + offset;

    let mut asmproc_flags = Vec::from(&all_args[..sep0]);
    let compiler = &all_args[sep0..sep1];
    let assembler_args = &all_args[sep1 + 1..sep2];
    let assembler_sh = assembler_args
        .iter()
        .map(|s| shlex::try_quote(s).unwrap().into_owned())
        .collect::<Vec<String>>()
        .join(" ");
    let mut compile_args = Vec::from(&all_args[sep2 + 1..]);
    let out_ind = compile_args.iter().position(|arg| arg == "-o").unwrap();
    let out_filename = &compile_args[out_ind + 1].clone();
    let out_file = Path::new(out_filename);
    compile_args.remove(out_ind + 1);
    compile_args.remove(out_ind);
    let in_file_str = compile_args.last().unwrap().clone();
    compile_args.pop();
    let in_file = Path::new(in_file_str.as_str());
    let in_dir = in_file.parent().unwrap();

    asmproc_flags.push(in_file.to_str().unwrap().to_string());
    let args = parse_args(&asmproc_flags, &compile_args)?;

    // Boolean for debugging purposes
    // Preprocessed files are temporary, set to True to keep a copy
    let keep_preprocessed_files = false;

    let asm_prelude_path = PathBuf::from("prelude.inc");

    let temp_dir = TempDir::with_prefix("asm_processor")?;
    let preprocessed_filename = format!(
        "preprocessed_{}.{}",
        uuid::Uuid::new_v4().to_string(),
        in_file
            .extension()
            .ok_or_else(|| anyhow::anyhow!("No file extension"))?
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("Invalid file extension"))?
    );
    let preprocessed_path = temp_dir.path().join(&preprocessed_filename);
    let preprocessed_file = File::create(&preprocessed_path)?;

    let res = run(&args, preprocessed_file, None)?;

    if keep_preprocessed_files {
        let kept_files_path = Path::new("asm_processor_preprocessed");
        fs::create_dir_all(kept_files_path)?;
        fs::copy(
            &preprocessed_path,
            Path::new("asm_processor_preprocessed").join(format!(
                "{}_{}",
                in_file.file_stem().unwrap().to_str().unwrap(),
                &preprocessed_filename
            )),
        )?;
    }

    // Run compiler
    let mut compile_command = Command::new(&compiler[0]);
    compile_command
        .args(&compile_args)
        .arg("-I")
        .arg(&in_dir)
        .arg("-o")
        .arg(&out_file)
        .arg(&preprocessed_path);

    let status = compile_command.status().expect(&format!(
        "Failed to compile file {}. Command line: {} {:?}",
        in_file.display(),
        compiler[0].clone(),
        compile_command
    ));

    if !status.success() {
        return Err(anyhow::anyhow!(
            "Failed to compile file {}. Command line: {} {:?}",
            in_file.display(),
            compiler[0].clone(),
            compile_command
        ));
    }

    let new_args = AsmProcArgs {
        post_process: Some(out_file.to_path_buf()),
        assembler: Some(assembler_sh),
        asm_prelude: Some(asm_prelude_path),
        ..args
    };

    run(&new_args, stdout(), Some(&res.functions))?;

    if !res.deps.is_empty() {
        let deps_file = out_file.with_extension("asmproc.d");
        let mut deps_file = File::create(&deps_file)?;

        writeln!(
            deps_file,
            "{}: {}",
            out_file.to_str().unwrap(),
            res.deps.join(" \\\n    ")
        )?;

        for dep in res.deps {
            writeln!(deps_file, "\n{}:", dep)?;
        }
    }

    Ok(())
}
