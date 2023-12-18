use crate::{
    builtins::{export_global_metods, export_top_level_builtins},
    function::Function,
    maths::export_math_lib,
    variant::Variant,
};
use ahash::AHashMap;
use anyhow::{anyhow, bail, Context, Ok, Result};
use std::{rc::Rc, vec};
#[derive(Debug, Clone)]
pub struct Memory {
    variables: Vec<AHashMap<Rc<str>, Variant>>,
    global_methods: AHashMap<Rc<str>, Variant>,
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            variables: vec![AHashMap::new()],
            global_methods: AHashMap::new(),
        }
    }

    pub fn with_builtins() -> Self {
        let context = export_top_level_builtins()
            .chain(std::iter::once(("Math".into(), export_math_lib())))
            .collect();

        Memory {
            variables: vec![context],
            global_methods: export_global_metods().collect(),
        }
    }

    pub fn push_empty_context(&mut self) {
        self.variables.push(AHashMap::new())
    }

    pub fn push_context(&mut self, context: AHashMap<Rc<str>, Variant>) {
        self.variables.push(context)
    }

    pub fn pop_context(&mut self) {
        // Avoid removing last context
        if self.variables.len() >= 2 {
            self.variables.pop();
        }
    }

    pub fn get_method(&self, identifier: &str) -> Result<&Variant> {
        self.global_methods
            .get(identifier)
            .ok_or_else(|| anyhow!("Method '{identifier}' not declared",))
    }

    pub fn get(&self, identifier: &str) -> Result<&Variant> {
        self.variables
            .iter()
            .rev()
            .find_map(|x| x.get(identifier))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn get_mut(&mut self, identifier: &str) -> Result<&mut Variant> {
        self.variables
            .iter_mut()
            .rev()
            .find_map(|x| x.get_mut(identifier))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn set(&mut self, identifier: &str, value: Variant) -> Result<()> {
        if value.is_error() {
            bail!("{value}");
        }
        match self
            .variables
            .iter_mut()
            .rev()
            .find_map(|x| x.get_mut(identifier))
        {
            Some(v) => *v = value,
            None => {
                self.variables
                    .last_mut()
                    .context("Fatal error: There is no current context in memory")?
                    .insert(identifier.into(), value);
            }
        }
        Ok(())
    }

    pub fn get_tests(&self) -> Vec<(Rc<str>, Rc<Function>)> {
        self.variables
            .iter()
            .flat_map(|i| {
                i.iter()
                    .filter(|(name, j)| name.starts_with("test_") && j.is_func())
                    .map(|(name, j)| (name.clone(), j.clone().unwrap_func()))
            })
            .collect()
    }
}
