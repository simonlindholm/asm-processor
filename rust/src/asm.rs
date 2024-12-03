use std::{collections::HashMap, iter};

use anyhow::Result;
use regex::Regex;

use crate::{Function, GlobalState};

#[derive(Clone, Debug)]
pub struct GlobalAsmBlock {
    fn_desc: String,
    cur_section: String,
    asm_conts: Vec<String>,
    late_rodata_asm_conts: Vec<String>,
    late_rodata_alignment: usize,
    late_rodata_alignment_from_context: bool,
    text_glabels: Vec<String>,
    fn_section_sizes: HashMap<String, usize>,
    fn_ins_inds: Vec<(usize, usize)>,
    glued_line: String,
    num_lines: usize,
}

impl GlobalAsmBlock {
    pub fn new(fn_desc: String) -> Self {
        Self {
            fn_desc,
            cur_section: ".text".to_string(),
            asm_conts: vec![],
            late_rodata_asm_conts: vec![],
            late_rodata_alignment: 0,
            late_rodata_alignment_from_context: false,
            text_glabels: vec![],
            fn_section_sizes: HashMap::from([
                (".text".to_string(), 0),
                (".data".to_string(), 0),
                (".bss".to_string(), 0),
                (".rodata".to_string(), 0),
                (".late_rodata".to_string(), 0),
            ]),
            fn_ins_inds: vec![],
            glued_line: String::new(),
            num_lines: 0,
        }
    }

    fn re_comment_replacer(caps: &regex::Captures) -> String {
        let s = caps[0].to_string();
        if s.starts_with("/") || s.starts_with("#") {
            " ".to_owned()
        } else {
            s
        }
    }

    fn count_quoted_size(line: &str, z: bool, real_line: &str, output_enc: &str) -> Result<usize> {
        let line = match encoding_rs::Encoding::for_label(output_enc.as_bytes()) {
            Some(encoding) => encoding.encode(line).0,
            None => return Err(anyhow::anyhow!("Unsupported encoding: {}", output_enc)),
        };
        let line = encoding_rs::WINDOWS_1252.decode_without_bom_handling(&line);
        let line = line.0.into_owned();

        let mut in_quote = false;
        let mut has_comma = true;
        let mut num_parts = 0;
        let mut ret = 0;
        let mut i = 0;
        let digits = "0123456789"; // 0-7 would be more sane, but this matches GNU as

        while i < line.chars().count() {
            let c = line.chars().nth(i).unwrap();
            i += 1;
            if !in_quote {
                if c == '"' {
                    in_quote = true;
                    if z && !has_comma {
                        return Err(anyhow::anyhow!(".asciiz with glued strings is not supported due to GNU as version diffs\n{}", real_line));
                    }
                    num_parts += 1;
                } else if c == ',' {
                    has_comma = true;
                }
            } else {
                if c == '"' {
                    in_quote = false;
                    has_comma = false;
                    continue;
                }
                ret += 1;
                if c != '\\' {
                    continue;
                }
                if i == line.len() {
                    return Err(anyhow::anyhow!(
                        "backslash at end of line not supported\n{}",
                        real_line
                    ));
                }
                let c = line.chars().nth(i).unwrap();
                i += 1;
                // (if c is in "bfnrtv", we have a real escaped literal)
                if c == 'x' {
                    // hex literal, consume any number of hex chars, possibly none
                    while i < line.len() && digits.contains(line.chars().nth(i).unwrap()) {
                        i += 1;
                    }
                } else if digits.contains(c) {
                    // octal literal, consume up to two more digits
                    let mut it = 0;
                    while i < line.len() && digits.contains(line.chars().nth(i).unwrap()) && it < 2
                    {
                        i += 1;
                        it += 1;
                    }
                }
            }
        }

        if in_quote {
            return Err(anyhow::anyhow!(
                "unterminated string literal\n{}",
                real_line
            ));
        }
        if num_parts == 0 {
            return Err(anyhow::anyhow!(".ascii with no string\n{}", real_line));
        }
        Ok(ret + if z { num_parts } else { 0 })
    }

    fn align(&mut self, n: usize) {
        while self.fn_section_sizes[&self.cur_section] % n != 0 {
            self.fn_section_sizes.insert(
                self.cur_section.clone(),
                self.fn_section_sizes[&self.cur_section] + 1,
            );
        }
    }

    fn add_sized(&mut self, size: isize, line: &str) -> Result<()> {
        if (self.cur_section == ".text" || self.cur_section == ".late_rodata") && size % 4 != 0 {
            return Err(anyhow::anyhow!("size must be a multiple of 4 {}", line));
        }

        if size < 0 {
            return Err(anyhow::anyhow!("size cannot be negative {}", line));
        }

        // add size to fn_section_sizes current section
        self.fn_section_sizes.insert(
            self.cur_section.clone(),
            self.fn_section_sizes[&self.cur_section] + size as usize,
        );

        if self.cur_section == ".text" {
            if self.text_glabels.is_empty() {
                return Err(anyhow::anyhow!(
                    ".text block without an initial glabel {}",
                    line
                ));
            }
            self.fn_ins_inds
                .push((self.num_lines - 1, size as usize / 4));
        }

        Ok(())
    }

    pub fn process_line(&mut self, line: &str, output_enc: &str) -> Result<()> {
        self.num_lines += 1;
        if let Some(stripped) = line.strip_suffix("\\") {
            self.glued_line = format!("{}{}", self.glued_line, stripped);
            return Ok(());
        }
        let mut line = self.glued_line.clone() + line;
        self.glued_line = String::new();

        let re_comment_or_string = Regex::new(r#"#.*|/\*.*?\*/|"(?:\\.|[^\\"])*""#).unwrap();
        let re_something = Regex::new(r"^[a-zA-Z0-9_]+:\s*").unwrap();

        let real_line = line.clone();
        line = re_comment_or_string
            .replace_all(&line, Self::re_comment_replacer)
            .into_owned();
        line = line.trim().to_string();
        line = re_something.replace_all(&line, "").into_owned();
        let mut changed_section = false;
        let mut emitting_double = false;

        if (line.starts_with("glabel ") || line.starts_with("jlabel "))
            && self.cur_section == ".text"
        {
            self.text_glabels
                .push(line.split_whitespace().nth(1).unwrap().to_string());
        }
        if line.is_empty() { // empty line
        } else if line.starts_with("glabel ")
            || line.starts_with("dlabel ")
            || line.starts_with("jlabel ")
            || line.starts_with("endlabel ")
            || (!line.contains(" ") && line.ends_with(":"))
        {
            // label
        } else if line.starts_with(".section")
            || matches!(
                line.as_str(),
                ".text" | ".data" | ".rdata" | ".rodata" | ".bss" | ".late_rodata"
            )
        {
            // section change
            self.cur_section = if line == ".rdata" {
                ".rodata".to_string()
            } else {
                line.split(',')
                    .next()
                    .unwrap()
                    .to_string()
                    .split_whitespace()
                    .last()
                    .unwrap()
                    .to_string()
            };

            match self.cur_section.as_str() {
                ".data" | ".text" | ".rodata" | ".late_rodata" | ".bss" => {}
                _ => return Err(anyhow::anyhow!("Unknown section: {}", self.cur_section)),
            }

            changed_section = true;
        } else if line.starts_with(".late_rodata_alignment") {
            if self.cur_section != ".late_rodata" {
                return Err(anyhow::anyhow!(format!(
                    ".late_rodata_alignment must occur within .late_rodata section\n{}",
                    real_line
                )));
            }

            let value = line.split_whitespace().nth(1).unwrap().parse::<usize>()?;
            if value != 4 && value != 8 {
                return Err(anyhow::anyhow!(format!(
                    ".late_rodata_alignment argument must be 4 or 8\n{}",
                    real_line
                )));
            }
            if self.late_rodata_alignment != 0 && self.late_rodata_alignment != value {
                return Err(anyhow::anyhow!(format!(
                    ".late_rodata_alignment alignment assumption conflicts with earlier .double directive. Make sure to provide explicit alignment padding."
                )));
            }
            self.late_rodata_alignment = value;
            changed_section = true;
        } else if line.starts_with(".incbin") {
            let siz = line.split(',').last().unwrap().trim().parse::<isize>()?;
            self.add_sized(siz, &real_line)?;
        } else if line.starts_with(".word")
            || line.starts_with(".gpword")
            || line.starts_with(".float")
        {
            self.align(4);

            self.add_sized(4 * line.split(',').count() as isize, &real_line)?;
        } else if line.starts_with(".double") {
            self.align(4);

            if self.cur_section == ".late_rodata" {
                let align8 = self.fn_section_sizes[&self.cur_section] % 8;
                // Automatically set late_rodata_alignment, so the generated C code uses doubles.
                // This gives us correct alignment for the transferred doubles even when the
                // late_rodata_alignment is wrong, e.g. for non-matching compilation.
                if self.late_rodata_alignment == 0 {
                    self.late_rodata_alignment = 8 - align8;
                    self.late_rodata_alignment_from_context = true;
                } else if self.late_rodata_alignment != 8 - align8 {
                    if self.late_rodata_alignment_from_context {
                        return Err(anyhow::anyhow!(format!(
                            "found two .double directives with different start addresses mod 8. Make sure to provide explicit alignment padding.\n{}", &real_line
                        )));
                    } else {
                        return Err(anyhow::anyhow!(format!(
                            ".double at address that is not 0 mod 8 (based on .late_rodata_alignment assumption). Make sure to provide explicit alignment padding.\n{}", real_line
                        )));
                    }
                }

                self.add_sized(8 * line.split(',').count() as isize, &real_line)?;
                emitting_double = true;
            }
        } else if line.starts_with(".space") {
            let siz = line.split_whitespace().nth(1).unwrap().parse::<isize>()?;
            self.add_sized(siz, &real_line)?;
        } else if line.starts_with(".balign") {
            let align = line.split_whitespace().nth(1).unwrap().parse::<isize>()?;
            if align != 4 {
                return Err(anyhow::anyhow!(format!(
                    "only .balign 4 is supported, found .balign {}",
                    align
                )));
            }
            self.align(4);
        } else if line.starts_with(".align") {
            let align = line.split_whitespace().nth(1).unwrap().parse::<isize>()?;
            if align != 2 {
                return Err(anyhow::anyhow!(format!(
                    "only .align 2 is supported, found .align {}",
                    align
                )));
            }
            self.align(4);
        } else if line.starts_with(".asci") {
            let z = line.starts_with(".asciz") || line.starts_with(".asciiz");
            self.add_sized(
                Self::count_quoted_size(&line, z, &real_line, output_enc)? as isize,
                &real_line,
            )?;
        } else if line.starts_with(".byte") {
            self.add_sized(line.split(',').count() as isize, &real_line)?;
        } else if line.starts_with(".half")
            || line.starts_with(".hword")
            || line.starts_with(".short")
        {
            self.align(2);
            self.add_sized(2 * line.split(',').count() as isize, &real_line)?;
        } else if line.starts_with(".size") {
        } else if line.starts_with('.') {
            return Err(anyhow::anyhow!(format!(
                "asm directive not supported {}",
                real_line
            )));
        } else {
            // Unfortunately, macros are hard to support for .rodata --
            // we don't know how how space they will expand to before
            // running the assembler, but we need that information to
            // construct the C code. So if we need that we'll either
            // need to run the assembler twice (at least in some rare
            // cases), or change how this program is invoked.
            // Similarly, we can't currently deal with pseudo-instructions
            // that expand to several real instructions.
            if self.cur_section != ".text" {
                return Err(anyhow::anyhow!(format!(
                    "instruction or macro call in non-.text section? not supported\n{}",
                    real_line
                )));
            }
            self.add_sized(4, &real_line)?;
        }

        if self.cur_section == ".late_rodata" {
            if !changed_section {
                if emitting_double {
                    self.late_rodata_asm_conts.push(".align 0".to_string());
                }
                self.late_rodata_asm_conts.push(real_line.clone());
                if emitting_double {
                    self.late_rodata_asm_conts.push(".align 2".to_string());
                }
            }
        } else {
            self.asm_conts.push(real_line.clone());
        }

        Ok(())
    }

    const MAX_FN_SIZE: usize = 100;

    pub fn finish(&self, state: &mut GlobalState) -> Result<(Vec<String>, Function)> {
        let mut src = vec!["".to_owned(); self.num_lines + 1];
        let mut late_rodata_dummy_bytes = vec![];
        let mut jtbl_rodata_size = 0;
        let mut late_rodata_fn_output = vec![];

        let num_instr = self.fn_section_sizes[".text"] / 4;

        if self.fn_section_sizes[".late_rodata"] > 0 {
            // Generate late rodata by emitting unique float constants.
            // This requires 3 instructions for each 4 bytes of rodata.
            // If we know alignment, we can use doubles, which give 3
            // instructions for 8 bytes of rodata.
            let size = self.fn_section_sizes[".late_rodata"] / 4;
            let mut skip_next = false;
            let mut needs_double = self.late_rodata_alignment != 0;
            let mut extra_mips1_nop = false;
            let (jtbl_size, jtbl_min_rodata_size) = match (state.pascal, state.mips1) {
                (true, true) => (9, 2),
                (true, false) => (8, 2),
                (false, true) => (11, 5),
                (false, false) => (9, 5),
            };

            for i in 0..size {
                if skip_next {
                    skip_next = false;
                    continue;
                }
                // Jump tables give 9 instructions (11 with -mips1) for >= 5 words of rodata,
                // and should be emitted when:
                // - -O2 or -O2 -g3 are used, which give the right codegen
                // - we have emitted our first .float/.double (to ensure that we find the
                //   created rodata in the binary)
                // - we have emitted our first .double, if any (to ensure alignment of doubles
                //   in shifted rodata sections)
                // - we have at least 5 words of rodata left to emit (otherwise IDO does not
                //   generate a jump table)
                // - we have at least 10 more instructions to go in this function (otherwise our
                //   function size computation will be wrong since the delay slot goes unused)
                if !needs_double
                    && state.use_jtbl_for_rodata
                    && i >= 1
                    && size - i >= jtbl_min_rodata_size
                    && num_instr - late_rodata_fn_output.len() >= jtbl_size + 1
                {
                    let line = if state.pascal {
                        let cases: String = (0..(size - i))
                            .map(|case| format!("{}: ;", case))
                            .collect::<Vec<String>>()
                            .join(" ");
                        format!("case 0 of {} otherwise end;", cases)
                    } else {
                        let cases: String = (0..(size - i))
                            .map(|case| format!("case {}:", case))
                            .collect::<Vec<String>>()
                            .join(" ");
                        format!("switch (*(volatile int*)0) {{ {} ; }}", cases)
                    };
                    late_rodata_fn_output.push(line);
                    late_rodata_fn_output.extend(iter::repeat("".to_owned()).take(jtbl_size - 1));
                    jtbl_rodata_size = (size - i) * 4;
                    extra_mips1_nop = i != 2;
                    break;
                }

                let dummy_bytes = state.next_late_rodata_hex();
                late_rodata_dummy_bytes.push(dummy_bytes);
                if self.late_rodata_alignment == 4 * ((i + 1) % 2 + 1) && i + 1 < size {
                    let dummy_bytes2 = state.next_late_rodata_hex();
                    late_rodata_dummy_bytes.push(dummy_bytes2);
                    let combined = [dummy_bytes, dummy_bytes2].concat().try_into().unwrap();
                    let fval = f64::from_be_bytes(combined);
                    let line = if state.pascal {
                        state.pascal_assignment_double("d", fval)
                    } else {
                        format!("*(volatile double*)0 = {:?};", fval)
                    };
                    late_rodata_fn_output.push(line);
                    skip_next = true;
                    needs_double = false;
                    if state.mips1 {
                        // mips1 does not have ldc1/sdc1
                        late_rodata_fn_output.push("".to_owned());
                        late_rodata_fn_output.push("".to_owned());
                    }
                    extra_mips1_nop = false;
                } else {
                    let fval = f32::from_be_bytes(dummy_bytes);
                    let line = if state.pascal {
                        state.pascal_assignment_float("f", fval)
                    } else {
                        format!("*(volatile float*)0 = {:?}f;", fval)
                    };
                    late_rodata_fn_output.push(line);
                    extra_mips1_nop = true;
                }
                late_rodata_fn_output.push("".to_owned());
                late_rodata_fn_output.push("".to_owned());
            }

            if state.mips1 && extra_mips1_nop {
                late_rodata_fn_output.push("".to_owned());
            }
        }

        let mut text_name = None;
        if self.fn_section_sizes[".text"] > 0 || !late_rodata_fn_output.is_empty() {
            let new_name = state.make_name("func");
            src[0] = state.func_prologue(&new_name);
            text_name = Some(new_name);
            src[self.num_lines] = state.func_epilogue();
            let instr_count = self.fn_section_sizes[".text"] / 4;
            if instr_count < state.min_instr_count {
                return Err(anyhow::anyhow!(format!("too short .text block",)));
            }
            let mut tot_emitted = 0;
            let mut tot_skipped = 0;
            let mut fn_emitted = 0;
            let mut fn_skipped = 0;
            let mut skipping = true;
            let mut rodata_stack: Vec<String> = late_rodata_fn_output.clone();
            rodata_stack.reverse();

            for (line, count) in &self.fn_ins_inds {
                for _ in 0..*count {
                    if fn_emitted > Self::MAX_FN_SIZE
                        && instr_count - tot_emitted > state.min_instr_count
                        && (rodata_stack.is_empty() || !rodata_stack.last().unwrap().is_empty())
                    {
                        // Don't let functions become too large. When a function reaches 284
                        // instructions, and -O2 -framepointer flags are passed, the IRIX
                        // compiler decides it is a great idea to start optimizing more.
                        // Also, Pascal cannot handle too large functions before it runs out
                        // of unique statements to write.
                        fn_emitted = 0;
                        fn_skipped = 0;
                        skipping = true;
                        let large_func_name = state.make_name("large_func");
                        src[*line] += format!(
                            " {} {} ",
                            state.func_epilogue(),
                            state.func_prologue(&large_func_name)
                        )
                        .as_str();
                    }

                    if skipping
                        && fn_skipped
                            < state.skip_instr_count
                                + (if !rodata_stack.is_empty() {
                                    state.prelude_if_late_rodata
                                } else {
                                    0
                                })
                    {
                        fn_skipped += 1;
                        tot_skipped += 1;
                    } else {
                        skipping = false;
                        if !rodata_stack.is_empty() {
                            src[*line] += rodata_stack.pop().unwrap().as_str();
                        } else if state.pascal {
                            src[*line] += state.pascal_assignment_int("i", 0).as_str();
                        } else {
                            src[*line] += "*(volatile int*)0 = 0;";
                        }
                    }
                    tot_emitted += 1;
                    fn_emitted += 1;
                }
            }

            if !rodata_stack.is_empty() {
                let size = late_rodata_fn_output.len() / 3;
                let available = instr_count - tot_skipped;
                return Err(anyhow::anyhow!(format!(
                    "late rodata to text ratio is too high: {} / {} must be <= 1/3\n
                    add .late_rodata_alignment (4|8) to the .late_rodata block
                    to double the allowed ratio.",
                    size, available
                )));
            }
        }

        let mut rodata_name = None;
        if self.fn_section_sizes[".rodata"] > 0 {
            if state.pascal {
                return Err(anyhow::anyhow!(format!(
                    ".rodata isn't supported with Pascal for now"
                )));
            }
            let new_name = state.make_name("rodata");
            src[self.num_lines] += format!(
                " const char {}[{}] = {{1}};",
                new_name, self.fn_section_sizes[".rodata"]
            )
            .as_str();
            rodata_name = Some(new_name);
        }

        let mut data_name = None;
        if self.fn_section_sizes[".data"] > 0 {
            let new_name = state.make_name("data");
            let line = if state.pascal {
                format!(
                    " var {}: packed array[1..{}] of char := [otherwise: 0];",
                    new_name, self.fn_section_sizes[".data"]
                )
            } else {
                format!(
                    " char {}[{}] = {{1}};",
                    new_name, self.fn_section_sizes[".data"]
                )
            };
            src[self.num_lines] += line.as_str();
            data_name = Some(new_name);
        }

        let mut bss_name = None;
        if self.fn_section_sizes[".bss"] > 0 {
            let new_name = state.make_name("bss");
            if state.pascal {
                return Err(anyhow::anyhow!(format!(
                    ".bss isn't supported with Pascal for now"
                )));
            }
            src[self.num_lines] +=
                format!(" char {}[{}];", new_name, self.fn_section_sizes[".bss"]).as_str();
            bss_name = Some(new_name);
        }

        let ret_fn = Function {
            text_glabels: self.text_glabels.clone(),
            asm_conts: self.asm_conts.clone(),
            late_rodata_dummy_bytes,
            jtbl_rodata_size,
            late_rodata_asm_conts: self.late_rodata_asm_conts.clone(),
            fn_desc: self.fn_desc.clone(),
            data: HashMap::from([
                (
                    ".text".to_string(),
                    (text_name, self.fn_section_sizes[".text"]),
                ),
                (
                    ".data".to_string(),
                    (data_name, self.fn_section_sizes[".data"]),
                ),
                (
                    ".rodata".to_string(),
                    (rodata_name, self.fn_section_sizes[".rodata"]),
                ),
                (
                    ".bss".to_string(),
                    (bss_name, self.fn_section_sizes[".bss"]),
                ),
            ]),
        };

        Ok((src, ret_fn))
    }
}
