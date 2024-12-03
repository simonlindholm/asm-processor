mod asm;
mod elf;

use std::{
    collections::HashMap,
    fmt::Debug,
    fs::{self, read_to_string, File},
    io::{stdout, Write},
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result};
use asm::GlobalAsmBlock;
use clap::{Parser, ValueEnum};
use elf::ElfFile;
use encoding_rs::Encoding;
use regex::Regex;
use temp_dir::TempDir;

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
            min_instr_count,
            skip_instr_count,
            use_jtbl_for_rodata,
            prelude_if_late_rodata,
            mips1,
            pascal,
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
            '}'.to_string()
        }
    }

    fn pascal_assignment_float(&mut self, tp: &str, val: f32) -> String {
        self.valuectr += 1;
        let address = (8 * self.valuectr) & 0x7FFF;
        format!("v{} := p{}({}); v{}^ := {:?};", tp, tp, address, tp, val)
    }

    fn pascal_assignment_double(&mut self, tp: &str, val: f64) -> String {
        self.valuectr += 1;
        let address = (8 * self.valuectr) & 0x7FFF;
        format!("v{} := p{}({}); v{}^ := {:?};", tp, tp, address, tp, val)
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
    #[clap(long)]
    drop_mdebug_gptab: bool,

    /// change static symbol visibility
    #[clap(long)]
    convert_statics: Option<SymbolVisibility>,

    /// force processing of files without GLOBAL_ASM blocks
    #[clap(long)]
    force: bool,

    /// Replace floats with their encoded hexadecimal representation in CutsceneData data
    #[clap(long)]
    encode_cutscene_data_float_encoding: bool,

    #[clap(long)]
    framepointer: bool,

    #[clap(long)]
    mips1: bool,

    #[clap(long)]
    g3: bool,

    #[clap(long = "KPIC")]
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
    let mut output_lines: Vec<String> = vec![format!("#line 1 \"{}\" ", infile_path.display())];
    let mut deps: Vec<String> = vec![];

    let mut is_cutscene_data = false;
    let mut is_early_include = false;
    let mut start_index: Option<usize> = None;

    let cutscene_re = Regex::new(r"CutsceneData (.|\n)*\[\] = \{")?;

    for (line_no, line) in read_to_string(infile_path)?.lines().enumerate() {
        let line_no = line_no + 1;
        let mut raw_line = line.trim().to_owned();
        let line = raw_line.trim_start();

        // Print exactly one output line per source line, to make compiler
        // errors have correct line numbers. These will be overridden with
        // reasonable content further down.
        output_lines.push("".to_owned());

        if let Some(ref mut gasm) = global_asm {
            if line.starts_with(')') {
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
        } else if ((line.starts_with("GLOBAL_ASM(\"") || line.starts_with("#pragma GLOBAL_ASM(\""))
            && line.ends_with("\")"))
            || ((line.starts_with("INCLUDE_ASM(\"") || line.starts_with("INCLUDE_RODATA(\""))
                && line.contains("\",")
                && line.ends_with(");"))
        {
            let (prologue, fname) = if line.starts_with("INCLUDE_") {
                // INCLUDE_ASM("path/to", functionname);
                let (before, after) = line.split_once("\",").unwrap();
                let fname = format!(
                    "{}/{}.s",
                    before[before.find('(').unwrap() + 2..].to_owned(),
                    after.trim()[..after.len() - 3].trim()
                );

                if line.starts_with("INCLUDE_RODATA") {
                    (vec![".section .rodata".to_string()], fname)
                } else {
                    (vec![], fname)
                }
            } else {
                // GLOBAL_ASM("path/to/file.s")
                let fname = line[line.find('(').unwrap() + 2..line.len() - 2].to_string();
                (vec![], fname)
            };

            let mut gasm = GlobalAsmBlock::new(fname.clone());
            for line2 in prologue {
                gasm.process_line(line2.trim_end(), &output_enc)?;
            }

            if !Path::new(&fname).exists() {
                // The GLOBAL_ASM block might be surrounded by an ifdef, so it's
                // not clear whether a missing file actually represents a compile
                // error. Pass the responsibility for determining that on to the
                // compiler by emitting a bad include directive. (IDO treats
                // #error as a warning for some reason.)
                let output_lines_len = output_lines.len();
                output_lines[output_lines_len - 1] = format!("#include \"GLOBAL_ASM:{}\"", fname);
                continue;
            }

            for line2 in read_to_string(&fname)?.lines() {
                gasm.process_line(line2.trim_end(), &output_enc)?;
            }

            let (src, fun) = gasm.finish(&mut state)?;
            let output_lines_len = output_lines.len();
            output_lines[output_lines_len - 1] = src.join("");
            asm_functions.push(fun);
            deps.push(fname);
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
                String::from_utf8(res.output.clone())?,
                line_no + 1,
                infile_path.file_name().unwrap().to_str().unwrap()
            );

            let output_lines_len = output_lines.len();
            output_lines[output_lines_len - 1] = res_str;
        } else {
            if args.encode_cutscene_data_float_encoding {
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

    let out_data = if encode {
        let newline_encoded = match Encoding::for_label(output_enc.as_bytes()) {
            Some(encoding) => encoding.encode("\n").0,
            None => return Err(anyhow::anyhow!("Unsupported encoding")),
        };

        let mut data = vec![];
        for line in output_lines {
            let line_encoded = match Encoding::for_label(output_enc.as_bytes()) {
                Some(encoding) => encoding.encode(&line).0,
                None => {
                    return Err(anyhow::anyhow!("Unsupported encoding"));
                }
            };
            data.write_all(&line_encoded)?;
            data.write_all(&newline_encoded)?;
        }
        data
    } else {
        let str = format!("{}\n", output_lines.join("\n"));

        str.as_bytes().to_vec()
    };

    Ok(RunResult {
        functions: asm_functions,
        deps,
        output: out_data,
    })
}

#[derive(Default)]
struct RunResult {
    functions: Vec<Function>,
    deps: Vec<String>,
    output: Vec<u8>,
}

fn run(
    args: &AsmProcArgs,
    mut outfile: impl Write,
    in_functions: Option<&[Function]>,
    use_default_asm_prelude: bool,
) -> Result<RunResult> {
    if args.post_process.is_none() {
        let res: RunResult = parse_source(&args.filename, args, true)?;
        outfile.write_all(&res.output)?;
        return Ok(res);
    } else {
        let objfile = args.post_process.clone().unwrap();

        let assembler = args
            .assembler
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Assembler command is required when post-processing"))?;

        let functions = if let Some(funcs) = in_functions {
            funcs.to_vec()
        } else {
            let res = parse_source(&args.filename, args, true)?;
            res.functions
        };

        if (functions.is_empty()) && !args.force {
            return Ok(RunResult::default());
        }

        let asm_prelude = if use_default_asm_prelude {
            include_str!("../../prelude.inc").to_string()
        } else {
            match &args.asm_prelude {
                Some(prelude) => {
                    let res = fs::read_to_string(prelude);
                    if let Ok(res) = res {
                        res
                    } else {
                        return Err(anyhow::anyhow!("Failed to read asm prelude"));
                    }
                }
                None => String::new(),
            }
        };

        ElfFile::fixup_objfile(
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

    let filename_str = args.filename.to_str().unwrap();

    let is_pascal = filename_str.ends_with(".p")
        || filename_str.ends_with(".pas")
        || filename_str.ends_with(".pp");

    if is_pascal && !(args.opt == OptLevel::O1 || args.opt == OptLevel::O2 || args.g3) {
        Err(anyhow::anyhow!(
            "Pascal is only supported together with -O1, -O2 or -O2 -g3"
        ))
        .context("Invalid arguments")?;
    }

    args.pascal = is_pascal;

    Ok(args)
}

fn main() -> Result<()> {
    let os_args: Vec<String> = std::env::args().collect();

    let all_args = os_args[1..].to_vec();
    let sep0 = all_args
        .iter()
        .position(|arg| !arg.starts_with('-'))
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
    let in_dir = fs::canonicalize(in_file.parent().unwrap())?;

    asmproc_flags.push(in_file.to_str().unwrap().to_string());
    asmproc_flags.insert(0, "clap is complicated".to_string());
    let args = parse_args(&asmproc_flags, &compile_args)?;

    // Boolean for debugging purposes
    // Preprocessed files are temporary, set to True to keep a copy
    let keep_preprocessed_files = false;

    let temp_dir = TempDir::with_prefix("asm_processor")?;
    let preprocessed_filename = format!(
        "preprocessed_{}.{}",
        uuid::Uuid::new_v4(),
        in_file
            .extension()
            .ok_or_else(|| anyhow::anyhow!("No file extension"))?
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("Invalid file extension"))?
    );
    let preprocessed_path = temp_dir.path().join(&preprocessed_filename);
    let preprocessed_file = File::create(&preprocessed_path)?;

    let res = run(&args, preprocessed_file, None, false)?;

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
        .arg(in_dir)
        .arg("-o")
        .arg(out_file)
        .arg(&preprocessed_path);

    let status = compile_command.status().unwrap_or_else(|_| {
        panic!(
            "Failed to compile file {}. Command line: {} {:?}",
            in_file.display(),
            compiler[0].clone(),
            compile_command
        )
    });

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
        ..args
    };

    run(&new_args, stdout(), Some(&res.functions), true)?;

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
            writeln!(deps_file, "\n{dep}:")?;
        }
    }

    Ok(())
}
