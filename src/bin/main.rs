
use anyhow::anyhow;
use anyhow::Result;
use new_interpreter::memory::Memory;
use new_interpreter::parser::expr_parser;
use std::env;
use std::fs;
use mimalloc_rust::GlobalMiMalloc;


#[global_allocator]
static GLOBAL_MIMALLOC: GlobalMiMalloc = GlobalMiMalloc;


fn main() -> Result<()> {
    let args: Vec<_> = env::args().collect();
    if args.len() == 2 {
        let code = fs::read_to_string(&args[1])?;
        let ast = expr_parser::program(&code)?;
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory)?;
        //dbg!(memory);
        Ok(())
    } else {
        Err(anyhow!("No path to program received"))
    }
}
