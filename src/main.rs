mod expr;
mod interpreter;
mod parser;
mod scanner;
mod token;

use std::env;
use std::fmt::Display;
use std::fs;
use std::path::Path;
use std::process::{ExitCode, Termination};

use interpreter::Interpret as _;
use parser::Parser;
use scanner::Scanner;
use token::Token;

pub(crate) trait Report {
    fn report(&mut self, line: usize, location: &str, msg: impl Display);

    fn error(&mut self, span: Span<'_>, msg: impl Display);
}

pub(crate) enum Span<'a> {
    Line(usize),
    Token(&'a Token),
}

impl Span<'_> {
    #[inline]
    pub fn line(&self) -> usize {
        match self {
            Self::Line(line) => *line,
            Self::Token(token) => token.line,
        }
    }
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

        "parse" => {
            let file_contents = read_file_contents(filename);

            let scanner = Scanner::new(file_contents);

            let tokens = match scanner.tokenize() {
                Ok(tokens) => tokens,
                Err((_, error)) => return error.report(),
            };

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

            let scanner = Scanner::new(file_contents);

            let tokens = match scanner.tokenize() {
                Ok(tokens) => tokens,
                Err((_, error)) => return error.report(),
            };

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
