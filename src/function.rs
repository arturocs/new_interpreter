use crate::expression::Expression;
use crate::memory::Memory;
use crate::variant::{Type, Variant};
use anyhow::{bail, Result};
use itertools::{EitherOrBoth, Itertools};
use ustr::Ustr;
use std::fmt;
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Function {
    pub name: Option<Ustr>,
    pub arg_names: Box<[(Ustr, Option<Expression>)]>,
    pub body: Box<[Expression]>,
}
impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let args = self
            .arg_names
            .iter()
            .map(|(name, value)| match value {
                Some(v) => format!("{name} = {v}",),
                None => name.to_string(),
            })
            .join(", ");

        let body: String = self.body.iter().join("\n\t");
        if let Some(n) = &self.name {
            write!(f, "fn {n}({args}) {{\n\t{body}\t\n}}")
        } else if self.body.len() <= 1 {
            write!(f, "|{args}| {body}")
        } else {
            write!(f, "|{args}| {{\n\t{body}\t\n}}")
        }
    }
}
impl Function {
    pub fn anonymous(args: Vec<(Ustr, Option<Expression>)>, body: Vec<Expression>) -> Self {
        Function {
            name: None,
            arg_names: args.into(),
            body: body.into(),
        }
    }

    pub fn new(
        name: &str,
        args: Vec<(Ustr, Option<Expression>)>,
        body: Vec<Expression>,
    ) -> Self {
        Function {
            name: Some(name.into()),
            arg_names: args.into(),
            body: body.into(),
        }
    }

    pub fn is_method(&self) -> bool {
        self.arg_names
            .first()
            .map(|i| i.0.as_ref() == "self")
            .unwrap_or(false)
    }

    pub fn call(&self, arg_values: &[Variant], variables: &mut Memory) -> Result<Variant> {
        let args_without_self = &self.arg_names[self.is_method() as usize..];
        let context: Result<Vec<_>> = args_without_self
            .iter()
            .zip_longest(arg_values.iter())
            .map(|i| match i {
                EitherOrBoth::Both((name, _), value) => Ok((name.clone(), value.clone())),
                EitherOrBoth::Left((name, Some(v))) => Ok((name.clone(), v.evaluate(variables)?)),
                EitherOrBoth::Left((name, None)) => bail!("Missing argument {name}"),
                EitherOrBoth::Right(_) => match &self.name {
                    Some(name) => bail!("Function {name} called with too many arguments"),
                    None => bail!("Annonymous function called with too many arguments"),
                },
            })
            .collect();

        let context = context?.into_iter();

        variables.push_context(context);
        let result = Expression::evaluate_expr_sequence(variables, &self.body);
        variables.pop_context();

        result
    }
}

type BoxedFn = Box<dyn Fn(&[Variant], &mut Memory) -> Result<Variant>>;
pub struct NativeFunction {
    pub name: Option<Ustr>,
    method_of: Box<[Type]>,
    function: BoxedFn,
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
        let type_ = if self.method_of.is_empty() {
            "function"
        } else {
            "method"
        };
        if let Some(name) = &self.name {
            write!(f, "{} {}()", type_, name)
        } else {
            let p = &self.function as *const _;
            write!(f, "Anonymous {type_} at {p:?}")
        }
    }
}

impl NativeFunction {
    pub fn new(
        name: &str,
        f: impl Fn(&[Variant], &mut Memory) -> Result<Variant> + 'static,
    ) -> Self {
        NativeFunction {
            name: Some(name.into()),
            method_of: vec![].into_boxed_slice(),
            function: Box::new(f),
        }
    }

    pub fn anonymous(f: impl Fn(&[Variant], &mut Memory) -> Result<Variant> + 'static) -> Self {
        NativeFunction {
            name: None,
            method_of: vec![].into_boxed_slice(),
            function: Box::new(f),
        }
    }

    pub fn method(
        name: &str,
        f: impl Fn(&[Variant], &mut Memory) -> Result<Variant> + 'static,
        method_of: Vec<Type>,
    ) -> Self {
        NativeFunction {
            name: Some(name.into()),
            method_of: method_of.into(),
            function: Box::new(f),
        }
    }

    pub fn is_method(&self) -> bool {
        !self.method_of.is_empty()
    }

    pub fn call(&self, args: &[Variant], memory: &mut Memory) -> Result<Variant> {
        if self.method_of.is_empty() {
            return (self.function)(args, memory);
        }
        let Some(v) = args.first() else {
            bail!("Cannot call {self} without arguments");
        };
        self.method_of
            .contains(&v.get_type())
            .then(|| (self.function)(args, memory))
            .unwrap_or_else(|| bail!("Cannot call {self} on variant {v}"))
    }
}
