use anyhow::bail;
use anyhow::Result;
use itertools::Itertools;
use mimalloc::MiMalloc;
use new_interpreter::runner::{run_file, run_tests};
use std::env;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> Result<()> {
    let args = env::args().collect_vec();
    match args.iter().map(|i| i.as_str()).collect_tuple() {
        Some((_, "run", path)) => run_file(path).map(|_| ())?,
        Some((_, "test", path)) => run_tests(path)?,
        _ => bail!("Incorrect number of arguments"),
    }
    Ok(())
}
