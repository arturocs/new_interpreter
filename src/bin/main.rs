use anyhow::anyhow;
use anyhow::Result;
use itertools::Itertools;
use mimalloc_rust::GlobalMiMalloc;
use new_interpreter::memory::Memory;
use new_interpreter::parser::expr_parser;
use std::env;
use std::fs;

#[global_allocator]
static GLOBAL_MIMALLOC: GlobalMiMalloc = GlobalMiMalloc;

fn main() -> Result<()> {
    let args: Vec<_> = env::args().collect();
    if args.len() == 2 {
        let code = fs::read_to_string(&args[1])?;
        let filtered_comments = code
            .lines()
            .map(|s| s.find("//").map(|i| &s[..i]).unwrap_or(s))
            .join("\n");
        let ast = expr_parser::expr_sequence(&filtered_comments)?;
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory)?;
        //dbg!(memory);
        Ok(())
    } else {
        Err(anyhow!("No path to program received"))
    }
}
