mod postprocess;
mod preprocess;

use std::{
    borrow::Cow,
    fmt::{Debug, Display},
    fs::{self, File},
    io::{stdout, Write},
    path::{Path, PathBuf},
    process::Command,
    str::FromStr,
};

use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use enum_map::{Enum, EnumMap};
use temp_dir::TempDir;

use postprocess::fixup_objfile;
use preprocess::parse_source;

#[derive(Clone, Debug)]
enum Encoding {
    Latin1,
    Custom(&'static encoding_rs::Encoding),
}

impl Encoding {
    fn encode<'a>(&self, s: &'a str) -> Result<Cow<'a, [u8]>> {
        match self {
            Encoding::Latin1 => {
                if encoding_rs::mem::is_str_latin1(s) {
                    return Ok(encoding_rs::mem::encode_latin1_lossy(s));
                }
            }
            Encoding::Custom(enc) => {
                let (ret, _, failed) = enc.encode(s);
                if !failed {
                    return Ok(ret);
                }
            }
        }
        Err(anyhow::anyhow!("Failed to encode string: {}", s))
    }
}

impl FromStr for Encoding {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "latin1" {
            Ok(Encoding::Latin1)
        } else {
            match encoding_rs::Encoding::for_label(s.as_bytes()) {
                Some(enc) => Ok(Encoding::Custom(enc)),
                None => Err(format!("Unsupported encoding: {}", s)),
            }
        }
    }
}

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
    #[clap(long)]
    asm_prelude: Option<PathBuf>,

    /// input encoding
    #[clap(long, default_value = "latin1", required = false)]
    input_enc: Encoding,

    /// output encoding
    #[clap(long, default_value = "latin1", required = false)]
    output_enc: Encoding,

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

#[derive(Copy, Clone, Eq, PartialEq, Debug, Enum)]
enum OutputSection {
    Text,
    Data,
    Rodata,
    Bss,
}

impl OutputSection {
    fn as_str(&self) -> &'static str {
        match self {
            OutputSection::Text => ".text",
            OutputSection::Data => ".data",
            OutputSection::Rodata => ".rodata",
            OutputSection::Bss => ".bss",
        }
    }
}

impl Display for OutputSection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Clone, Debug)]
struct Function {
    text_glabels: Vec<String>,
    asm_conts: Vec<String>,
    late_rodata_dummy_bytes: Vec<[u8; 4]>,
    jtbl_rodata_size: usize,
    late_rodata_asm_conts: Vec<String>,
    fn_desc: String,
    data: EnumMap<OutputSection, (Option<String>, usize)>,
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
    let out_ind = compile_args
        .iter()
        .position(|arg| arg == "-o")
        .expect("Missing -o argument");
    let out_filename = &compile_args[out_ind + 1].clone();
    let out_file = Path::new(out_filename);
    compile_args.remove(out_ind + 1);
    compile_args.remove(out_ind);
    let in_file_str = compile_args.last().unwrap().clone();
    compile_args.pop();
    let in_file = Path::new(in_file_str.as_str());
    let in_dir = fs::canonicalize(in_file.parent().unwrap().join("."))?;

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
