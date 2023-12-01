use crate::{builtins::export_top_level_builtins, maths::export_math_lib, variant::Variant};
use ahash::AHashMap;
use anyhow::{anyhow, bail, Context, Ok, Result};
use std::{rc::Rc, vec};
#[derive(Debug, Clone)]
pub struct Memory(Vec<AHashMap<Rc<str>, Variant>>);

impl Memory {
    pub fn new() -> Self {
        Memory(vec![AHashMap::new()])
    }

    pub fn static_with_builtins() -> &'static mut Self {
        Box::leak(Box::new(Self::with_builtins()))
    }

    pub fn with_builtins() -> Self {
        let context = export_top_level_builtins()
            .chain(std::iter::once(("Math".into(), export_math_lib())))
            .collect();

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

    pub fn get_mut(&mut self, identifier: &str) -> Result<&mut Variant> {
        self.0
            .iter_mut()
            .rev()
            .find_map(|x| x.get_mut(identifier))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn set(&mut self, identifier: &str, value: Variant) -> Result<()> {
        if value.is_error() {
            bail!("{value}");
        }
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
