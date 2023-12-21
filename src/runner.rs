use crate::{function::Function, memory::Memory, parser::expr_parser, variant::Variant};
use anyhow::{bail, Result};
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
    let metadata = fs::metadata(path)?;
    if metadata.is_dir() {
        let paths = fs::read_dir(path)?;
        for path in paths {
            let path = path?.path();
            let path = path.to_str().unwrap();
            run_tests_in_file(path)?;
        }
    } else if metadata.is_file() {
        run_tests_in_file(path)?;
    } else {
        bail!("Path {path} is not a file or directory")
    }
    Ok(())
}

pub fn run_tests_in_file(path: &str) -> Result<()> {
    let (_result, mut memory) = run_file(path)?;
    let tests: Vec<(Rc<str>, Rc<Function>)> = memory.get_tests();
    let n_tests = tests.len();
    if n_tests == 0 {
        println!("\nNo tests found in {path}\n");
        return Ok(());
    }
    println!("\nFound {n_tests} tests in {path}:\n");
    let mut passed = 0;
    let failed_msg = "Failed!".red();
    let ok_msg = "Ok!".green();
    for (test_name, test_function) in tests {
        print!("Running test {test_name}... ");
        match test_function.call(&[], &mut memory) {
            Ok(Variant::Error(e)) => println!("{failed_msg}: {e}"),
            Err(e) => println!("{failed_msg}: {e}"),
            Ok(_) => {
                passed += 1;
                println!("{ok_msg}")
            }
        }
    }
    println!("\nPassed {passed}/{n_tests} tests");
    println!("Failed {}/{n_tests} tests\n", n_tests - passed);
    Ok(())
}
