use anyhow::bail;
use anyhow::Result;
use itertools::Itertools;
use mimalloc::MiMalloc;
use new_interpreter::runner::{
    get_files_and_apply_runner, run_benches_in_file, run_file, run_tests_in_file,
};
use std::env;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> Result<()> {
    let args = env::args().collect_vec();
    match args.iter().map(|i| i.as_str()).collect_tuple() {
        Some((_, "run", path)) => run_file(path).map(|_| ())?,
        Some((_, "test", path)) => get_files_and_apply_runner(path, run_tests_in_file)?,
        Some((_, "bench", path)) => get_files_and_apply_runner(path, run_benches_in_file)?,
        _ => bail!("Incorrect number of arguments"),
    }
    Ok(())
}
