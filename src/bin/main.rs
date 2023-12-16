use anyhow::bail;
use anyhow::Result;
use itertools::Itertools;
use mimalloc::MiMalloc;
use new_interpreter::memory::Memory;
use new_interpreter::parser::expr_parser;
use std::env;
use std::fs;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> Result<()> {
    let args = env::args().collect_vec();
    if args.len() == 2 {
        let code = fs::read_to_string(&args[1])?;
        let filtered_comments = code
            .lines()
            .map(|s| s.find("//").map(|i| &s[..i]).unwrap_or(s))
            .join("\n");
        let ast = expr_parser::expr_sequence(&filtered_comments)?;
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory)?;
        Ok(())
    } else {
        bail!("No path to program received")
    }
}
