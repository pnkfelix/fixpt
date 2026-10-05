//! `fixpt-symbolize`: macOS `sample`'s output with the frames in fixpt's
//! own machine code named (`fixpt_tidy::symbolize`).
//!
//!     FIXPT_SYMBOLS=/tmp/syms.%p fixpt …        names written as code is placed
//!     sample PID 10 -file /tmp/sample.txt
//!     fixpt-symbolize /tmp/syms.PID… [-- SAMPLE]   SAMPLE, or the standard input
//!
//! Every file before `--` (or all but the last, without it) is a map; the
//! named sample, with a summary by name at the top of the stack, is
//! written to the standard output.

use std::io::Read;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (maps, sample) = match args.iter().position(|a| a == "--") {
        Some(i) => (&args[..i], args.get(i + 1).cloned()),
        None if args.len() >= 2 => (&args[..args.len() - 1], args.last().cloned()),
        None => (&args[..], None),
    };
    if maps.is_empty() {
        eprintln!("fixpt-symbolize: usage: fixpt-symbolize MAP… [-- SAMPLE]   (SAMPLE, or the standard input)");
        return ExitCode::FAILURE;
    }
    let mut map = String::new();
    for m in maps {
        match std::fs::read_to_string(m) {
            Ok(t) => map.push_str(&t),
            Err(e) => {
                eprintln!("fixpt-symbolize: {m}: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    let text = match sample {
        Some(path) => std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}")),
        None => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s).map(|_| s).map_err(|e| e.to_string())
        }
    };
    match text {
        Ok(text) => {
            print!("{}", fixpt_tidy::symbolize::symbolize(&fixpt_tidy::symbolize::Symbols::parse(&map), &text));
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("fixpt-symbolize: {e}");
            ExitCode::FAILURE
        }
    }
}
