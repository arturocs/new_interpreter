use crate::{
    builtins::{export_global_metods, export_top_level_builtins},
    function::Function,
    maths::export_math_lib,
    variant::{Dictionary, Variant},
};
use ahash::AHashMap;
use anyhow::{anyhow, Ok, Result};
use std::{rc::Rc, vec};
#[derive(Debug, Clone)]
pub struct Memory {
    context_delimiters: Vec<usize>,
    variables: Vec<(Rc<str>, Variant)>,
    global_methods: AHashMap<Rc<str>, Variant>,
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            context_delimiters: vec![],
            variables: vec![],
            global_methods: AHashMap::new(),
        }
    }

    pub fn with_builtins() -> Self {
        let context = export_top_level_builtins()
            .chain(std::iter::once(("Math".into(), export_math_lib())))
            .collect();

        Memory {
            context_delimiters: vec![],
            variables: context,
            global_methods: export_global_metods().collect(),
        }
    }

    pub fn push_empty_context(&mut self) {
        self.context_delimiters.push(self.variables.len())
    }

    pub fn push_context(&mut self, context: impl Iterator<Item = (Rc<str>, Variant)>) {
        self.push_empty_context();
        self.variables.extend(context)
    }

    pub fn pop_context(&mut self) {
        // Avoid removing last context
        if self.context_delimiters.len() >= 1 {
            let start = self.context_delimiters.pop().unwrap();
            self.variables.truncate(start);
        } else {
            eprintln!("Warning: tried to pop context from empty stack")
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
            .find_map(|(name, value)| (name.as_ref() == identifier).then_some(value))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn get_mut(&mut self, identifier: &str) -> Result<&mut Variant> {
        self.variables
            .iter_mut()
            .rev()
            .find_map(|(name, value)| (name.as_ref() == identifier).then_some(value))
            .ok_or_else(|| anyhow!("Variable '{identifier}' not declared"))
    }

    pub fn set(&mut self, identifier: &str, value: Variant) -> Result<()> {
        match self
            .variables
            .iter_mut()
            .rev()
            .find_map(|(name, value)| (name.as_ref() == identifier).then_some(value))
        {
            Some(v) => *v = value,
            None => {
                self.variables.push((identifier.into(), value));
            }
        }
        Ok(())
    }

    pub fn get_tests(&self) -> Vec<(Rc<str>, Rc<Function>)> {
        self.variables
            .iter()
            .filter(|(name, j)| name.starts_with("test_") && j.is_func())
            .map(|(name, j)| (name.clone(), j.clone().unwrap_func()))
            .collect()
    }

    pub fn to_dict(&self) -> Dictionary {
        let builtins_len = Memory::with_builtins().variables.len();
        self.variables[builtins_len..]
            .iter()
            .map(|(name, value)| (Variant::str(name), value.clone()))
            .collect()
    }
}
