mod postprocess;
mod preprocess;

use std::{
    borrow::Cow,
    fmt::{Debug, Display},
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
    process::{exit, Command},
    str::FromStr,
};

use anyhow::Result;
use argp::{FromArgs, HelpStyle};
use enum_map::{Enum, EnumMap};
use temp_dir::TempDir;

use postprocess::fixup_objfile;
use preprocess::parse_source;

#[derive(Clone, Copy, Debug)]
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

    fn decode<'a>(&self, bytes: &'a [u8]) -> Result<Cow<'a, str>> {
        match self {
            Encoding::Latin1 => Ok(encoding_rs::mem::decode_latin1(bytes)),
            Encoding::Custom(enc) => {
                let (ret, _, failed) = enc.decode(bytes);
                if !failed {
                    Ok(ret)
                } else {
                    Err(anyhow::anyhow!("Failed to decode string: {}", ret))
                }
            }
        }
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

#[derive(Copy, Clone, Debug, PartialEq)]
enum ConvertStatics {
    No,
    Local,
    Global,
    GlobalWithFilename,
}

impl FromStr for ConvertStatics {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "no" => ConvertStatics::No,
            "local" => ConvertStatics::Local,
            "global" => ConvertStatics::Global,
            "global-with-filename" => ConvertStatics::GlobalWithFilename,
            _ => return Err("invalid value for symbol visibility".into()),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum OptLevel {
    O0,
    O1,
    O2,
    G,
    G3,
}

/// Pre-process .c files and post-process .o files to enable embedding MIPS assembly into IDO-compiled C.
#[derive(FromArgs)]
struct AsmProcArgs {
    /// Path to a file containing a prelude to the assembly file (with .set and .macro directives, e.g.)
    #[argp(option, arg_name = "FILE")]
    asm_prelude: Option<PathBuf>,

    /// Input encoding (default: latin1)
    #[argp(
        option,
        default = "Encoding::Latin1",
        from_str_fn(FromStr::from_str),
        arg_name = "ENCODING"
    )]
    input_enc: Encoding,

    /// Output encoding (default: latin1)
    #[argp(
        option,
        default = "Encoding::Latin1",
        from_str_fn(FromStr::from_str),
        arg_name = "ENCODING"
    )]
    output_enc: Encoding,

    /// Drop mdebug and gptab sections
    #[argp(switch)]
    drop_mdebug_gptab: bool,

    /// Change symbol visibility for static variables. Mode must be one of:
    /// no, local, global, global-with-filename (default: local)
    #[argp(
        option,
        default = "ConvertStatics::Local",
        from_str_fn(FromStr::from_str),
        arg_name = "MODE"
    )]
    convert_statics: ConvertStatics,

    /// Force processing of files without GLOBAL_ASM blocks
    #[argp(switch)]
    force: bool,

    /// Replace floats with their encoded hexadecimal representation in CutsceneData data
    #[argp(switch)]
    encode_cutscene_data_floats: bool,

    #[argp(
        positional,
        greedy,
        arg_name = "compiler... -- assembler... -- compiler flags"
    )]
    rest: Vec<String>,
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

struct CompileOpts {
    opt: OptLevel,
    framepointer: bool,
    mips1: bool,
    kpic: bool,
    pascal: bool,
}

fn extract_compiler_input_output(
    compile_args: &[String],
) -> Result<(PathBuf, PathBuf, Vec<String>), &'static str> {
    let mut compile_args: Vec<String> = compile_args.to_vec();
    let out_ind = compile_args
        .iter()
        .position(|arg| arg == "-o")
        .ok_or("missing -o argument")?;
    let out_filename = compile_args
        .get(out_ind + 1)
        .ok_or("missing argument after -o")?
        .clone();
    compile_args.remove(out_ind + 1);
    compile_args.remove(out_ind);

    let in_file_str = compile_args
        .last()
        .ok_or("missing input file argument")?
        .clone();
    compile_args.pop();

    let out_file: PathBuf = out_filename.into();
    let in_file: PathBuf = in_file_str.into();

    Ok((in_file, out_file, compile_args))
}

fn parse_compile_args(
    compile_args: &[String],
    in_file: &Path,
) -> Result<CompileOpts, &'static str> {
    let mut opt_flags = vec![];
    for x in compile_args {
        opt_flags.push(match x.as_str() {
            "-g" => OptLevel::G,
            "-O0" => OptLevel::O0,
            "-O1" => OptLevel::O1,
            "-O2" => OptLevel::O2,
            _ => continue,
        });
    }

    if opt_flags.len() != 1 {
        return Err("exactly one of -g/-O0/-O1/-O2 must be passed");
    }
    let mut opt = opt_flags[0];

    let mips1 = !compile_args.contains(&"-mips2".to_string());
    let framepointer = compile_args.contains(&"-framepointer".to_string());
    let kpic = compile_args.contains(&"-KPIC".to_string());
    if compile_args.contains(&"-g3".to_string()) {
        if opt != OptLevel::O2 {
            return Err("-g3 is only supported together with -O2");
        }
        opt = OptLevel::G3;
    }

    if mips1 && (!matches!(opt, OptLevel::O1 | OptLevel::O2) || framepointer) {
        return Err("-mips1 is only supported together with -O1 or -O2");
    }

    let in_file_str = in_file.to_string_lossy();
    let pascal = in_file_str.ends_with(".p")
        || in_file_str.ends_with(".pas")
        || in_file_str.ends_with(".pp");

    if pascal && !matches!(opt, OptLevel::O1 | OptLevel::O2 | OptLevel::G3) {
        return Err("Pascal is only supported together with -O1, -O2 or -O2 -g3");
    }

    Ok(CompileOpts {
        opt,
        framepointer,
        mips1,
        kpic,
        pascal,
    })
}

fn parse_rest(rest: &[String]) -> Option<(&[String], &[String], &[String])> {
    let mut iter = rest.splitn(3, |x| *x == "--");
    let compiler = iter.next()?;
    let assembler = iter.next()?;
    let compile_args = iter.next()?;
    assert!(iter.next().is_none());
    Some((compiler, assembler, compile_args))
}

fn main() -> Result<()> {
    let args: AsmProcArgs = argp::parse_args_or_exit(&HelpStyle {
        short_usage: true,
        ..HelpStyle::default()
    });
    let Some((compiler, assembler, compile_args)) = parse_rest(&args.rest) else {
        eprintln!(
            "Usage: asm-processor [options] <compiler...> -- <assembler...> -- <compiler flags...>"
        );
        eprintln!("Run asm-processor --help for more information.");
        exit(1);
    };

    let (in_file, out_file, compile_args) = extract_compiler_input_output(compile_args)
        .unwrap_or_else(|err| {
            eprintln!("Failed to parse compiler flags: {}", err);
            exit(1);
        });

    let opts = parse_compile_args(&compile_args, &in_file).unwrap_or_else(|err| {
        eprintln!("Unsupported compiler flags: {}", err);
        exit(1);
    });

    let assembler_sh = assembler
        .iter()
        .map(|s| shlex::try_quote(s).unwrap().into_owned())
        .collect::<Vec<String>>()
        .join(" ");

    let in_dir = fs::canonicalize(in_file.parent().unwrap().join("."))?;

    // Boolean for debugging purposes
    // Preprocessed files are temporary, set to True to keep a copy
    let keep_preprocessed_files = false;

    let temp_dir = TempDir::with_prefix("asm_processor")?;
    let preprocessed_filename = format!(
        "preprocessed_{}",
        in_file.file_name().unwrap().to_str().unwrap()
    );
    let preprocessed_path = temp_dir.path().join(&preprocessed_filename);
    let mut preprocessed_file = File::create(&preprocessed_path)?;

    let res = parse_source(&in_file, &args, &opts, true)?;
    preprocessed_file.write_all(&res.output)?;

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
        .arg(&out_file)
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

    if !res.functions.is_empty() || args.force {
        let prelude_str;
        let asm_prelude = match &args.asm_prelude {
            Some(prelude) => {
                if let Ok(res) = fs::read_to_string(prelude) {
                    prelude_str = res;
                    &prelude_str
                } else {
                    return Err(anyhow::anyhow!("Failed to read asm prelude"));
                }
            }
            None => include_str!("../../prelude.inc"),
        };

        fixup_objfile(
            &out_file,
            &res.functions,
            asm_prelude,
            &assembler_sh,
            &args.output_enc,
            args.drop_mdebug_gptab,
            args.convert_statics,
        )?;
    }

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
