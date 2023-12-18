use anyhow::bail;
use anyhow::Result;
use itertools::Itertools;
use mimalloc::MiMalloc;
use new_interpreter::memory::Memory;
use new_interpreter::parser::expr_parser;
use new_interpreter::variant::Variant;
use std::env;
use std::fs;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn run_file(path: &str) -> Result<(Variant, Memory)> {
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

fn run_tests(path: &str) -> Result<()> {
    let (_result, mut memory) = run_file(path)?;
    let tests = memory.get_tests();
    println!("Found {} tests in {path}", tests.len());
    for (test_name, test_function) in tests {
        print!("Running test {test_name}... ");
        match test_function.call(&[], &mut memory) {
            Ok(Variant::Error(e)) => println!("Failed!: {e}"),
            Err(e) => println!("Failed!: {e}"),
            Ok(_) => println!("Ok!"),
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let args = env::args().collect_vec();
    match args.iter().map(|i| i.as_str()).collect_tuple() {
        Some((_, "run", path)) => run_file(path).map(|_| ())?,
        Some((_, "test", path)) => run_tests(path)?,
        _ => bail!("Incorrect number of arguments"),
    }
    Ok(())
}
