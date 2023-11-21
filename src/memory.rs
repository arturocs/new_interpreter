use crate::{builtins, variant::{Variant, Type}};
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
        let sum: fn(&[Variant], &mut Memory) -> Variant = builtins::sum;
        let context = vec![
            ("sum", sum, None),
            ("prod", builtins::prod, None),
            ("min", builtins::min, None),
            ("max", builtins::max, None),
            ("sort", builtins::sort, Some(vec![Type::Vec])),
            ("sort_by", builtins::sort_by, Some(vec![Type::Vec])),
            ("print", builtins::print, None),
            ("input", builtins::input, None),
            ("push", builtins::push, Some(vec![Type::Vec])),
            ("range", builtins::range, None),
            ("contains", builtins::contains, Some(vec![Type::Vec, Type::Dict])),
            ("join", builtins::join, Some(vec![Type::Vec, Type::Iterator])),
            ("map", builtins::map, Some(vec![Type::Vec, Type::Iterator])),
            ("filter", builtins::filter, Some(vec![Type::Vec, Type::Iterator])),
            ("to_vec", builtins::to_vec, Some(vec![Type::Vec, Type::Iterator])),
        ]
        .into_iter()
        .map(|(name, f, method_of)| {
            if let Some(v) = method_of {
                (name.into(), Variant::method(name, f, v))
            } else {
                (name.into(), Variant::native_fn(f))
            }
        })
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
