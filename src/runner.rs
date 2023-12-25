use crate::{function::Function, memory::Memory, parser::expr_parser, variant::Variant};
use anyhow::{bail, Result};
use colored::Colorize;
use itertools::Itertools;
use std::time::{Duration, Instant};
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

pub fn get_files_and_apply_runner(
    path: &str,
    runner_function: impl Fn(&str) -> Result<()>,
) -> Result<()> {
    let metadata = fs::metadata(path)?;
    if metadata.is_dir() {
        let paths = fs::read_dir(path)?;
        for path in paths {
            let path = path?.path();
            let path = path.to_str().unwrap();
            runner_function(path)?;
        }
    } else if metadata.is_file() {
        runner_function(path)?;
    } else {
        bail!("Path {path} is not a file or directory")
    }
    Ok(())
}

fn run_bench(
    name: &str,
    func: &Function,
    memory: &mut Memory,
    warmup_seconds: u64,
    bench_seconds: u64,
) -> Result<()> {
    println!("Running {name}...");

    let warmup_time = Duration::from_secs(warmup_seconds);
    let mut iterations = 0;
    let start = Instant::now();
    while warmup_time > start.elapsed() {
        func.call(&[], memory)?;
        iterations += 1;
    }

    let average_time = warmup_time.as_secs_f64() / iterations as f64;
    let bench_iterations = (bench_seconds as f64 / average_time).trunc() as u32;
    let mut times = Vec::with_capacity(bench_iterations as usize);
    for _ in 0..bench_iterations {
        let t = Instant::now();
        func.call(&[], memory)?;
        times.push(t.elapsed());
    }
    let average_time = times.iter().sum::<Duration>() / bench_iterations as u32;
    let time_formated = format!("{average_time:?}").bold();
    let colored_name = name.green().bold();
    println!("Ran {colored_name} {bench_iterations} times. Average time: {time_formated}\n");
    Ok(())
}

pub fn run_benches_in_file(path: &str) -> Result<()> {
    let (_result, mut memory) = run_file(path)?;
    let benches: Vec<(Rc<str>, Rc<Function>)> = memory.get_functions_starting_with("bench_");
    let n_benches = benches.len();
    if n_benches == 0 {
        println!("\nNo benches found in {path}\n");
        return Ok(());
    }
    println!("\nFound {n_benches} benches in {path}:\n");
    for (bench_name, bench_function) in benches {
        run_bench(&bench_name, &bench_function, &mut memory, 3, 5)?;
    }
    Ok(())
}

pub fn run_tests_in_file(path: &str) -> Result<()> {
    let (_result, mut memory) = run_file(path)?;
    let tests: Vec<(Rc<str>, Rc<Function>)> = memory.get_functions_starting_with("test_");
    let n_tests = tests.len();
    if n_tests == 0 {
        println!("\nNo tests found in {path}\n");
        return Ok(());
    }
    println!("\nFound {n_tests} tests in {path}:\n");
    let mut passed = 0;
    let failed_msg = "Failed!".bold().red();
    let ok_msg = "Ok!".bold().green();
    for (test_name, test_function) in tests {
        print!("Running {}... ",test_name.bold());
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
