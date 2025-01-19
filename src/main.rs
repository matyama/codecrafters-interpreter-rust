use std::io::{BufWriter, Write as _};
use std::path::Path;
use std::process::{ExitCode, Termination};

use crate::lexer::Lexer;
use crate::token::EOF;
use crate::tree_walk::{Ast, Expr};

mod bytecode_vm;
mod error;
mod lexer;
mod span;
mod token;
mod tree_walk;

fn read_file_contents(file: impl AsRef<Path>) -> String {
    let file = file.as_ref();
    std::fs::read_to_string(file).unwrap_or_else(|_| {
        eprintln!("Failed to read file {file:?}");
        String::new()
    })
}

fn main() -> impl Termination {
    let args = std::env::args().collect::<Vec<_>>();

    if args.len() < 3 {
        eprintln!("Usage: {} <command> <filename>", args[0]);
        return ExitCode::from(64);
    }

    let command = &args[1];
    let filename = &args[2];

    let source = read_file_contents(filename);

    match command.as_str() {
        "tokenize" => {
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

        "parse" => match source.parse::<Ast<Expr>>() {
            Ok(Ast { tree, .. }) => {
                println!("{tree}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("{error}");
                error.report()
            }
        },

        "evaluate" => {
            let analyze = |ast| tree_walk::resolve(&source, ast);

            let ast = match source.parse().and_then(analyze) {
                Ok(ast) => ast,
                Err(error) => return error.report(),
            };

            let stdout = std::io::stdout().lock();
            let mut writer = BufWriter::new(stdout);

            let result = tree_walk::evaluate(ast, &mut writer);

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
            let analyze = |ast| tree_walk::resolve(&source, ast);

            let ast = match source.parse().and_then(analyze) {
                Ok(ast) => ast,
                Err(error) => {
                    eprintln!("{error}");
                    return error.report();
                }
            };

            let stdout = std::io::stdout().lock();
            let mut writer = BufWriter::new(stdout);

            let result = tree_walk::interpret(ast, &mut writer);

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
