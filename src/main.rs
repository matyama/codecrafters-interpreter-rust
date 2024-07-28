mod scanner;

use std::env;
use std::fs;

use crate::scanner::Scanner;

fn main() {
    let args = env::args().collect::<Vec<_>>();

    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
        return;
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

            if let Ok(tokens) = scanner.tokenize() {
                for token in tokens {
                    println!("{token}");
                }
            }
        }
        _ => {
            eprintln!("Unknown command: {command}");
        }
    }
}
