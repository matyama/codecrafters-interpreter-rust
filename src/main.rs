mod error;
mod interpreter;
mod ir;
mod lexer;
mod parser;
mod span;
mod token;

use std::env;
use std::fs;
use std::io::{self, BufWriter, Write as _};
use std::path::Path;
use std::process::{ExitCode, Termination};

use ir::{Expr, Program};
use lexer::Lexer;
use token::EOF;

fn read_file_contents(file: impl AsRef<Path>) -> String {
    let file = file.as_ref();
    fs::read_to_string(file).unwrap_or_else(|_| {
        eprintln!("Failed to read file {file:?}");
        String::new()
    })
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
            let source = read_file_contents(filename);

            let mut exit_code = ExitCode::SUCCESS;

            for token in Lexer::new(&source) {
                match token {
                    Ok(token) => println!("{token}"),
                    Err(error) => {
                        eprintln!("{error}");
                        exit_code = error.report();
                    }
                }
            }

            println!("{EOF}");

            exit_code
        }

        "parse" => {
            let source = read_file_contents(filename);

            match source.parse::<Expr>() {
                Ok(expr) => {
                    println!("{expr}");
                    ExitCode::SUCCESS
                }
                Err(error) => {
                    eprintln!("{error}");
                    error.report()
                }
            }
        }

        "evaluate" => {
            let source = read_file_contents(filename);

            let expr = match source.parse::<Expr>() {
                Ok(expr) => expr,
                Err(error) => return error.report(),
            };

            let stdout = io::stdout().lock();
            let mut writer = BufWriter::new(stdout);

            let result = interpreter::evaluate(expr, &mut writer);

            if let Err(error) = writer.flush() {
                eprintln!("{error}");
                return ExitCode::FAILURE;
            }

            match result {
                Ok(value) => {
                    println!("{value}");
                    ExitCode::SUCCESS
                }
                Err(error) => {
                    eprintln!("{error}");
                    error.report()
                }
            }
        }

        "run" => {
            let source = read_file_contents(filename);

            let prog = match source.parse::<Program>() {
                Ok(prog) => prog,
                Err(error) => {
                    eprintln!("{error}");
                    return error.report();
                }
            };

            let stdout = io::stdout().lock();
            let mut writer = BufWriter::new(stdout);

            let result = interpreter::interpret(prog, &mut writer);

            if let Err(error) = writer.flush() {
                eprintln!("{error}");
                return ExitCode::FAILURE;
            }

            if let Err(error) = result {
                eprintln!("{error}");
                error.report()
            } else {
                ExitCode::SUCCESS
            }
        }

        _ => {
            eprintln!("Unknown command: {command}");
            ExitCode::FAILURE
        }
    }
}
