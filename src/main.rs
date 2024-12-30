mod error;
mod expr;
mod interpreter;
mod lexer;
mod parser;
mod span;
mod token;

use std::env;
use std::fmt::Display;
use std::fs;
use std::path::Path;
use std::process::{ExitCode, Termination};

use interpreter::Interpret as _;
use lexer::Lexer;
use parser::Parser;
use token::EOF;

pub(crate) trait Report {
    fn report(&mut self, line: usize, location: &str, msg: impl Display);

    fn error<T: Display, M: Display>(&mut self, span: Span<T>, msg: M);
}

pub(crate) enum Span<T> {
    Eof(usize),
    Token(T, usize),
}

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
            let file_contents = read_file_contents(filename);

            let mut exit_code = ExitCode::SUCCESS;

            for token in Lexer::new(&file_contents) {
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
            let file_contents = read_file_contents(filename);

            // TODO: pass token stream directly into Parser and propagate errors
            // (i.e., don't collect/iterate here)
            let mut tokens = Vec::new();
            let mut exit_code = None;

            for token in Lexer::new(&file_contents) {
                match token {
                    Ok(token) => tokens.push(token),
                    Err(error) => {
                        eprintln!("{error}");
                        exit_code = Some(error.report());
                    }
                }
            }

            if let Some(exit_code) = exit_code {
                return exit_code;
            }

            let parser = Parser::new(tokens);

            match parser.parse() {
                Ok(expr) => {
                    println!("{expr}");
                    ExitCode::SUCCESS
                }
                Err(error) => error.report(),
            }
        }

        "evaluate" => {
            let file_contents = read_file_contents(filename);

            let mut tokens = Vec::new();
            let mut exit_code = None;

            for token in Lexer::new(&file_contents) {
                match token {
                    Ok(token) => tokens.push(token),
                    Err(error) => {
                        eprintln!("{error}");
                        exit_code = Some(error.report());
                    }
                }
            }

            if let Some(exit_code) = exit_code {
                return exit_code;
            }

            let parser = Parser::new(tokens);

            let expr = match parser.parse() {
                Ok(expr) => expr,
                Err(error) => return error.report(),
            };

            match expr.interpret() {
                Ok(value) => {
                    println!("{value}");
                    ExitCode::SUCCESS
                }
                Err(error) => error.report(),
            }
        }

        _ => {
            eprintln!("Unknown command: {command}");
            ExitCode::FAILURE
        }
    }
}
