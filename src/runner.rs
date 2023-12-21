use crate::{function::Function, memory::Memory, parser::expr_parser, variant::Variant};
use anyhow::Result;
use colored::Colorize;
use itertools::Itertools;
use std::{fs, rc::Rc};
pub fn run_file(path: &str) -> Result<(Variant, Memory)> {
    let code = fs::read_to_string(path)?;
    let filtered_comments = code
        .lines()
        .map(|s| s.find("//").map(|i| &s[..i]).unwrap_or(s))
        .join("\n");
    let ast = expr_parser::expr_sequence(&filtered_comments)?;
    let mut memory = Memory::with_builtins();
    let result = ast.evaluate(&mut memory)?;
    Ok((result, memory))
}

pub fn run_tests(path: &str) -> Result<()> {
    let (_result, mut memory) = run_file(path)?;
    let tests: Vec<(Rc<str>, Rc<Function>)> = memory.get_tests();
    let n_tests = tests.len();
    println!("Found {n_tests} tests in {path}:\n");
    let mut passed = 0;
    for (test_name, test_function) in tests {
        print!("Running test {test_name}... ");
        match test_function.call(&[], &mut memory) {
            Ok(Variant::Error(e)) => println!("{}: {e}", "Failed!".red()),
            Err(e) => println!("{}: {e}", "Failed!".red()),
            Ok(_) => {
                passed += 1;
                println!("{}", "Ok!".green())
            }
        }
    }
    println!("\nPassed {passed}/{n_tests} tests");
    println!("Failed {}/{n_tests} tests", n_tests - passed);
    Ok(())
}
