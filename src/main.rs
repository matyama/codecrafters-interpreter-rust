mod scanner;

use std::env;
use std::fmt::Display;
use std::fs;

use crate::scanner::Scanner;
use std::process::{ExitCode, Termination};

pub(crate) trait Report {
    fn report(&mut self, line: usize, location: &str, msg: impl Display);

    fn error(&mut self, line: usize, msg: impl Display);
}

fn main() -> impl Termination {
    let args = env::args().collect::<Vec<_>>();

    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
        return ExitCode::from(64);
    }

    let command = &args[1];
    let filename = &args[2];

    match command.as_str() {
        "tokenize" => {
            let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
                eprintln!("Failed to read file {filename}");
                String::new()
            });

            let scanner = Scanner::new(file_contents);

            let (tokens, exit_code) = match scanner.tokenize() {
                Ok(tokens) => (tokens, ExitCode::SUCCESS),
                Err((tokens, error)) => (tokens, error.report()),
            };

            for token in tokens {
                println!("{token}");
            }

            exit_code
        }
        _ => {
            eprintln!("Unknown command: {command}");
            ExitCode::FAILURE
        }
    }
}
