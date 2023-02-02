use crate::{builtins, variant::Variant};
use ahash::AHashMap;
use anyhow::{anyhow, Context, Ok, Result};
use std::rc::Rc;
#[derive(Debug, Clone)]
pub struct Memory(Vec<AHashMap<Rc<str>, Variant>>);

impl Memory {
    pub fn new() -> Self {
        Memory(vec![AHashMap::new()])
    }

    pub fn with_builtins() -> Self {
        let context = AHashMap::from([
            ("sum".into(), Variant::native_fn(builtins::sum)),
            ("prod".into(), Variant::native_fn(builtins::prod)),
            ("min".into(), Variant::native_fn(builtins::min)),
            ("max".into(), Variant::native_fn(builtins::max)),
            ("sort".into(), Variant::native_fn(builtins::sort)),
            //("sort_by".into(), Variant::native_fn(builtins::sort_by))
            ("print".into(), Variant::native_fn(builtins::print)),
            ("input".into(), Variant::native_fn(builtins::input)),
        ]);
        Memory(vec![context])
    }

    pub fn push_empty_context(&mut self) {
        self.0.push(AHashMap::new())
    }

    pub fn push_context(&mut self, context: AHashMap<Rc<str>, Variant>) {
        self.0.push(context)
    }

    pub fn pop_context(&mut self) {
        // Avoid removing last context
        if self.0.len() >= 2 {
            self.0.pop();
        }
    }

    pub fn get(&self, identifier: &str) -> Result<&Variant> {
        self.0
            .iter()
            .rev()
            .find_map(|x| x.get(identifier))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn set(&mut self, identifier: &str, value: Variant) -> Result<()> {
        match self.0.iter_mut().rev().find_map(|x| x.get_mut(identifier)) {
            Some(v) => *v = value,
            None => {
                self.0
                    .last_mut()
                    .context("Fatal error: There is no current context in memory")?
                    .insert(identifier.into(), value);
            }
        }
        Ok(())
    }
}
