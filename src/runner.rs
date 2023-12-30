use crate::{function::Function, memory::Memory, parser::expr_parser, variant::Variant};
use anyhow::{bail, Result};
use colored::Colorize;
use itertools::Itertools;
use std::io::{self, Write};
use std::time::{Duration, Instant};
use std::{fs, rc::Rc};

pub fn remove_comments(code: &str) -> String {
    code.lines()
        .map(|s| s.find("//").map(|i| &s[..i]).unwrap_or(s))
        .join("\n")
}

pub fn run_file(path: &str) -> Result<(Variant, Memory)> {
    let code = fs::read_to_string(path)?;
    let filtered_comments = remove_comments(&code);
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
    warmup_seconds: f64,
    bench_seconds: f64,
) -> Result<()> {
    print!("Running {name}: Warming up for {warmup_seconds:.4}s ...");
    io::stdout().flush().unwrap();

    let warmup_time = Duration::from_secs_f64(warmup_seconds);
    let mut iterations = 0;
    let start = Instant::now();
    while warmup_time > start.elapsed() {
        func.call(&[], memory)?;
        iterations += 1;
    }
    let average_time = warmup_time.as_secs_f64() / iterations as f64;
    let bench_iterations = (bench_seconds / average_time).round() as u32;
    let expected_duration = Duration::from_secs_f64(bench_iterations as f64 * average_time);

    let running_message = format!("\rRunning {name}: Collecting {bench_iterations} samples. Estimated time {expected_duration:.4?}");
    print!("{running_message}");
    io::stdout().flush().unwrap();

    let mut times = Duration::from_secs(0);
    for _ in 0..bench_iterations {
        let t = Instant::now();
        func.call(&[], memory)?;
        times += t.elapsed();
    }

    let average_time = times / bench_iterations;
    let time_formated = format!("{average_time:?}").bold();
    let colored_name = name.green().bold();
    let padding = " ".repeat(running_message.len());

    println!(
        "\rRan {colored_name} {bench_iterations} times. Average time: {time_formated}{padding}"
    );
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
        run_bench(&bench_name, &bench_function, &mut memory, 3., 5.)?;
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
        print!("Running {}... ", test_name.bold());
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
