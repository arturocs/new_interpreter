use crate::expression::{Expression, Memory};
use crate::variant::Variant;
use ahash::AHashMap;
use anyhow::{anyhow, Result};
use std::fmt;

#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct Function {
    pub args: Vec<String>,
    pub body: Vec<Expression>,
}

impl Function {
    pub fn new(args: Vec<String>, body: Vec<Expression>) -> Self {
        Function { args, body }
    }

    pub fn call(&self, args: &[Variant], variables: Memory) -> Result<Variant> {
        let context: AHashMap<_, _> = self
            .args
            .iter()
            .zip(args.iter())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        variables.push(context);

        let result = self
            .body
            .iter()
            .map(|exp| exp.evaluate(variables))
            .last()
            .ok_or_else(|| anyhow!("Function call without body"))
            .and_then(|i| i);
        variables.pop();
        result
    }
}

#[derive(Clone)]
pub struct NativeFunction(fn(&[Variant]) -> Variant);
impl fmt::Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NativeFunction")
            .field(&(self as *const _))
            .finish()
    }
}

impl NativeFunction {
    pub fn new(f: fn(&[Variant]) -> Variant) -> Self {
        NativeFunction(f)
    }

    pub fn call(&self, args: &[Variant]) -> Variant {
        self.0(args)
    }
}
