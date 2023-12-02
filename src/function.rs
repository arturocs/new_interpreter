use crate::expression::Expression;
use crate::memory::Memory;
use crate::variant::{Type, Variant};
use ahash::AHashMap;
use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Function {
    pub name: Option<Box<str>>,
    pub arg_names: Box<[Rc<str>]>,
    pub body: Box<[Expression]>,
}
impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let args = self.arg_names.iter().join(", ");
        let body: String = self.body.iter().join("\n\t");
        if let Some(n) = &self.name {
            write!(f, "fn {n}({args}) {{\n\t{body}\t\n}}")
        } else {
            write!(f, "|{args}| {{\n\t{body}\t\n}}")
        }
    }
}
impl Function {
    pub fn anonymous(args: Vec<Rc<str>>, body: Vec<Expression>) -> Self {
        Function {
            name: None,
            arg_names: args.into(),
            body: body.into(),
        }
    }

    pub fn new(name: &str, args: Vec<Rc<str>>, body: Vec<Expression>) -> Self {
        Function {
            name: Some(name.into()),
            arg_names: args.into(),
            body: body.into(),
        }
    }

    pub fn is_method(&self) -> bool {
        self.arg_names
            .first()
            .map(|i| i.as_ref() == "self")
            .unwrap_or(false)
    }

    pub fn call(&self, args: &[Variant], variables: &mut Memory) -> Result<Variant> {
        let args_without_self = &self.arg_names[self.is_method() as usize..];
        let context: AHashMap<_, _> = args_without_self
            .iter()
            .zip(args.iter())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        variables.push_context(context);

        let result = self
            .body
            .iter()
            .map(|exp| exp.evaluate(variables))
            .last()
            .ok_or_else(|| anyhow!("Function call without body"))
            .and_then(|i| i);
        variables.pop_context();
        result
    }
}

pub struct NativeFunction {
    pub name: Option<Box<str>>,
    method_of: Option<Box<[Type]>>,
    function: Box<dyn Fn(&[Variant], &mut Memory) -> Variant>,
}
impl fmt::Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NativeFunction")
            .field("name", &self.name)
            .field("method_of", &self.method_of)
            .field("function", &(&self.function as *const _))
            .finish()
    }
}

impl fmt::Display for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let type_ = if self.method_of.is_none() {
            "function"
        } else {
            "method"
        };
        if let Some(name) = &self.name {
            write!(f, "{} {}()", type_, name)
        } else {
            let p = &self.function as *const _;
            write!(f, "Anonymous {} at {:?}", type_, p)
        }
    }
}

impl NativeFunction {
    pub fn new(name: &str, f: impl Fn(&[Variant], &mut Memory) -> Variant + 'static) -> Self {
        NativeFunction {
            name: Some(name.into()),
            method_of: None,
            function: Box::new(f),
        }
    }

    pub fn anonymous(f: impl Fn(&[Variant], &mut Memory) -> Variant + 'static) -> Self {
        NativeFunction {
            name: None,
            method_of: None,
            function: Box::new(f),
        }
    }

    pub fn method(
        name: &str,
        f: impl Fn(&[Variant], &mut Memory) -> Variant + 'static,
        method_of: Vec<Type>,
    ) -> Self {
        NativeFunction {
            name: Some(name.into()),
            method_of: Some(method_of.into()),
            function: Box::new(f),
        }
    }

    pub fn is_method(&self) -> bool {
        self.method_of.is_some()
    }

    pub fn call(&self, args: &[Variant], memory: &mut Memory) -> Variant {
        let Some(types) = &self.method_of else {
            return (self.function)(args, memory);
        };
        let Some(v) = args.get(0) else {
            return Variant::error(format!("Cannot call {self} without arguments"));
        };
        types
            .contains(&v.get_type())
            .then(|| (self.function)(args, memory))
            .unwrap_or_else(|| Variant::error(format!("Cannot call {self} on variant {v:?}")))
    }
}
