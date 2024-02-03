use crate::{function::Function, memory::Memory, parser::expr_parser, variant::Variant};
use anyhow::{bail, Result};
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
use colored::Colorize;
use indexmap::IndexMap;
use itertools::Itertools;
use std::io::{self, Read, Seek, Write};
use std::path::Path;
use std::time::{Duration, Instant, SystemTime};
use std::{fs, rc::Rc};

pub fn remove_comments(code: &str) -> String {
    code.lines()
        .map(|s| s.find("//").map(|i| &s[..i]).unwrap_or(s))
        .join("\n")
}

fn print_parse_error(
    source_name: &str,
    source: &str,
    error: peg::error::ParseError<peg::str::LineCol>,
) {
    let a = ColorGenerator::new().next();
    let source = Source::from(source);
    let n_lines = source.lines().count() as i64;
    let context_labels = (-5..5).map(|i| {
        let offset = source
            .lines()
            .nth((error.location.line as i64 + i).clamp(0, n_lines) as usize)
            .unwrap()
            .offset();
        Label::new((source_name, offset..offset))
    });

    Report::build(ReportKind::Error, source_name, error.location.offset)
        .with_message("Error while parsing code")
        .with_label(
            Label::new((
                source_name,
                error.location.offset..error.location.offset + 1,
            ))
            .with_message(format!("Expected: {}", error.expected))
            .with_color(a),
        )
        .with_labels(context_labels)
        .finish()
        .print((source_name, source))
        .unwrap();
}

pub fn run_file(path: &str) -> Result<(Variant, Memory)> {
    let code = fs::read_to_string(path)?;
    let filtered_comments = remove_comments(&code);
    let parse_result = expr_parser::expr_sequence(&filtered_comments);
    match parse_result {
        Ok(ast) => {
            let mut memory = Memory::with_builtins();
            let result = ast.evaluate(&mut memory)?;
            Ok((result, memory))
        }
        Err(error) => {
            print_parse_error(path, &code, error);
            bail!("A problem occurred during parsing")
        }
    }
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
) -> Result<Duration> {
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
    Ok(average_time)
}

fn store_results_in_json(path: &str, times: IndexMap<String, Duration>) -> Result<()> {
    let current_time = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)?
        .as_millis()
        .to_string();
    let file_exists = Path::new(path).exists();
    let mut file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .read(true)
        .open(path)?;
    let mut v: IndexMap<String, IndexMap<String, Duration>> = IndexMap::new();
    if file_exists {
        let mut buf = String::new();
        file.read_to_string(&mut buf)?;
        file.rewind()?;
        v = serde_json::from_str(&buf)?;
    }
    v.insert(current_time, times);
    let data = serde_json::to_string_pretty(&v)?;
    file.write_all(data.as_bytes())?;
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

    let times = benches
        .into_iter()
        .map(|(bench_name, bench_function)| {
            Ok((
                format!("{path}/{bench_name}"),
                run_bench(&bench_name, &bench_function, &mut memory, 3., 5.)?,
            ))
        })
        .collect::<Result<IndexMap<_, _>>>()?;
    store_results_in_json("./bench_results.json", times)?;

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
