use crate::{
    memory::Memory,
    variant::{Dictionary, Variant},
};
use anyhow::{anyhow, bail, Context, Result};
use bstr::ByteSlice;
use itertools::Itertools;
use std::borrow::Cow;
use std::fmt;

#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum Expression {
    Value(Variant),
    Identifier(String),
    FunctionCall {
        function: Box<Expression>,
        arguments: Vec<Expression>,
    },
    Dictionary(Vec<(Expression, Expression)>),
    Vec(Vec<Expression>),

    //Binary Operations
    Mul(Box<(Expression, Expression)>),
    Div(Box<(Expression, Expression)>),
    Rem(Box<(Expression, Expression)>),
    Add(Box<(Expression, Expression)>),
    Sub(Box<(Expression, Expression)>),
    Eq(Box<(Expression, Expression)>),
    NotEq(Box<(Expression, Expression)>),
    Gt(Box<(Expression, Expression)>),
    Lt(Box<(Expression, Expression)>),
    Gtoe(Box<(Expression, Expression)>),
    Ltoe(Box<(Expression, Expression)>),
    And(Box<(Expression, Expression)>),
    Or(Box<(Expression, Expression)>),
    In(Box<(Expression, Expression)>),

    //Unary Operations
    Neg(Box<Expression>),
    Not(Box<Expression>),

    Block(Vec<Expression>),
    ExprSequence(Vec<Expression>),

    // First expression -> condition, second -> if body, third -> else body
    Conditional(Box<(Expression, Expression, Option<Expression>)>),
    // First expression -> indexable, second -> index
    Index(Box<(Expression, Expression)>),
    // First expression -> indexable, second -> index, third -> value
    IndexAssign(Box<(Expression, Expression, Expression)>),

    DestructureVecAssign {
        names: Vec<String>,
        value: Box<Expression>,
    },

    DestructureDictAssign {
        names: Vec<String>,
        value: Box<Expression>,
    },

    // First expression -> indexable, second -> index
    Dot(Box<(Expression, Expression)>),

    Fstring(Vec<Expression>),

    FunctionDeclaration {
        name: Box<str>,
        function: Variant,
    },
    // "statements"
    Declaration {
        name: String,
        value: Box<Expression>,
    },
    // First expression -> condition, second -> body
    While(Box<(Expression, Expression)>),

    For {
        i_name: String,
        // First expression -> iterable, second -> body
        iterable_and_body: Box<(Expression, Expression)>,
    },

    DestructureVecFor {
        names: Vec<String>,
        iterable_and_body: Box<(Expression, Expression)>,
    },

    DestructureDictFor {
        names: Vec<String>,
        iterable_and_body: Box<(Expression, Expression)>,
    },
}

impl fmt::Display for Expression {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Value(v) => {
                if v.is_str() {
                    write!(fmt, "\"{v}\"")
                } else {
                    write!(fmt, "{v}")
                }
            }
            Expression::Identifier(i) => write!(fmt, "{i}"),
            Expression::FunctionCall {
                function,
                arguments,
            } => {
                let args = arguments.iter().join(", ");
                write!(fmt, "{function}({args})",)
            }
            Expression::Dictionary(d) => {
                let content = d
                    .iter()
                    .map(|(v1, v2)| format!("\t{v1} : {v2}"))
                    .join(",\n");
                write!(fmt, "{{\n{content}\n}}",)
            }
            Expression::Vec(v) => {
                let values = v.iter().join(", ");
                write!(fmt, "[{values}]",)
            }
            Expression::Mul(o) => write!(fmt, "{} * {}", o.0, o.1),
            Expression::Div(o) => write!(fmt, "{} / {}", o.0, o.1),
            Expression::Rem(o) => write!(fmt, "{} % {}", o.0, o.1),
            Expression::Add(o) => write!(fmt, "{} + {}", o.0, o.1),
            Expression::Sub(o) => write!(fmt, "{} - {}", o.0, o.1),
            Expression::Eq(o) => write!(fmt, "{} == {}", o.0, o.1),
            Expression::NotEq(o) => write!(fmt, "{} != {}", o.0, o.1),
            Expression::Gt(o) => write!(fmt, "{} > {}", o.0, o.1),
            Expression::Lt(o) => write!(fmt, "{} < {}", o.0, o.1),
            Expression::Gtoe(o) => write!(fmt, "{} >= {}", o.0, o.1),
            Expression::Ltoe(o) => write!(fmt, "{} <= {}", o.0, o.1),
            Expression::And(o) => write!(fmt, "{} and {}", o.0, o.1),
            Expression::Or(o) => write!(fmt, "{} or {}", o.0, o.1),
            Expression::Neg(n) => write!(fmt, "!{n}"),
            Expression::Not(n) => write!(fmt, "-{n}"),
            Expression::Block(b) => {
                write!(fmt, "{{\n\t{}\t\n}}", b.iter().join("\n"))
            }
            Expression::ExprSequence(p) => {
                write!(fmt, "{}", p.iter().join("\n"))
            }
            Expression::Conditional(c) => {
                if let Some(c2) = &c.2 {
                    write!(fmt, "if {} {} else {}", c.0, c.1, c2)
                } else {
                    write!(fmt, "if {} {}", c.0, c.1)
                }
            }
            Expression::Index(i) => write!(fmt, "{}[{}]", i.0, i.1),
            Expression::IndexAssign(i) => write!(fmt, "{}[{}] = {}", i.0, i.1, i.2),
            Expression::Dot(d) => write!(fmt, "{}.{}", d.0, d.1),
            Expression::Fstring(f) => {
                let is_str = |e: &_| match e {
                    Expression::Value(v) => v.is_str(),
                    _ => false,
                };
                let content = f
                    .iter()
                    .map(|i| {
                        is_str(i)
                            .then(|| i.to_string().trim_matches('"').into())
                            .unwrap_or_else(|| format!("{{{i}}}"))
                    })
                    .join("");
                write!(fmt, r#"f"{content}""#)
            }
            Expression::Declaration { name, value } => write!(fmt, "{name} = {value}"),
            Expression::While(w) => write!(fmt, "while {} {}", w.0, w.1),
            Expression::For {
                i_name,
                iterable_and_body,
            } => write!(
                fmt,
                "for {} in {} {}",
                i_name, iterable_and_body.0, iterable_and_body.1
            ),
            Expression::FunctionDeclaration { name: _, function } => write!(fmt, "{function}"),
            Expression::In(i) => write!(fmt, "{} in {}", i.0, i.1),
            Expression::DestructureVecAssign { names: _, value: _ } => todo!(),
            Expression::DestructureDictAssign { names: _, value: _ } => todo!(),
            Expression::DestructureVecFor {
                names: _,
                iterable_and_body: _,
            } => todo!(),
            Expression::DestructureDictFor {
                names: _,
                iterable_and_body: _,
            } => todo!(),
        }
    }
}

impl Expression {
    fn apply_binary_exp<'a>(
        variables: &mut Memory,
        (a, b): &'a (Expression, Expression),
        expr: fn(&Variant, &Variant) -> Result<Variant>,
    ) -> Result<Cow<'a, Variant>> {
        let lhs = a.evaluate(variables)?;
        let rhs = b.evaluate(variables)?;
        expr(&lhs, &rhs).map(Cow::Owned)
    }

    fn apply_unary_exp<'a>(
        variables: &mut Memory,
        i: &'a Expression,
        expr: fn(&Variant) -> Result<Variant>,
    ) -> Result<Cow<'a, Variant>> {
        let value = i.evaluate(variables)?;
        expr(&value).map(Cow::Owned)
    }

    fn apply_logical_exp<'a>(
        variables: &mut Memory,
        (a, b): &'a (Expression, Expression),
        expr: fn(&Variant, &Variant) -> bool,
    ) -> Result<Cow<'a, Variant>> {
        let lhs = a.evaluate(variables)?;
        let rhs = b.evaluate(variables)?;
        Ok(Cow::Owned(Variant::Bool(expr(&lhs, &rhs))))
    }

    fn evaluate_identifier<'a>(variables: &mut Memory, i: &str) -> Result<Cow<'a, Variant>> {
        variables.get(i).map(|i| Cow::Owned(i.clone()))
    }

    fn evaluate_function_call<'a>(
        variables: &mut Memory,
        function: &'a Expression,
        arguments: &'a [Expression],
    ) -> Result<Cow<'a, Variant>> {
        match &*function.evaluate(variables)? {
            Variant::NativeFunc(f) => {
                let evaluated_args = arguments
                    .iter()
                    .map(|e| e.evaluate(variables).map(|c| c.into_owned()))
                    .collect::<Result<Vec<_>>>()?;
                f.call(&evaluated_args, variables).map(Cow::Owned)
            }
            Variant::Func(f) => {
                let evaluated_args: Result<Vec<_>> = arguments
                    .iter()
                    .map(|e| e.evaluate(variables).map(|c| c.into_owned()))
                    .collect();
                f.call(&evaluated_args?, variables).map(Cow::Owned)
            }
            a => bail!("{a} is not a function"),
        }
    }

    pub fn evaluate_expr_sequence<'a>(
        variables: &mut Memory,
        statements: &'a [Expression],
    ) -> Result<Cow<'a, Variant>> {
        let results: Result<Vec<_>> = statements
            .iter()
            .map(|e| match e.evaluate(variables) {
                Ok(v) if matches!(&*v, Variant::Error(_)) => {
                    let err_str = v.to_string();
                    Err(anyhow!(
                        "{}",
                        err_str.trim_start_matches("Error: ").trim_matches('"')
                    ))
                }
                a => a,
            })
            .collect();
        let results = results?;
        let last = results.into_iter().last();
        last.context("No statements in scope")
    }

    fn evaluate_block<'a>(
        variables: &mut Memory,
        statements: &'a [Expression],
    ) -> Result<Cow<'a, Variant>> {
        variables.push_empty_context();
        let result = Self::evaluate_expr_sequence(variables, statements);
        variables.pop_context();
        result
    }

    fn evaluate_conditional<'a>(
        variables: &mut Memory,
        (condition, if_body, else_body): &'a (Expression, Expression, Option<Expression>),
    ) -> Result<Cow<'a, Variant>> {
        if *condition.evaluate(variables)? == Variant::Bool(true) {
            variables.push_empty_context();
            let result = if_body.evaluate(variables);
            variables.pop_context();
            result
        } else if let Some(body) = else_body {
            variables.push_empty_context();
            let result = body.evaluate(variables);
            variables.pop_context();
            result
        } else {
            Ok(Cow::Owned(Variant::error("No else body")))
        }
    }

    fn evaluate_index<'a>(
        variables: &mut Memory,
        (indexable, index): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        indexable
            .evaluate(variables)?
            .index(&*index.evaluate(variables)?)
            .map(|i| Cow::Owned(i.clone()))
    }

    fn evaluate_dot<'a>(
        variables: &mut Memory,
        indexable_and_index: &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let Expression::Value(index) = &indexable_and_index.1 else {
            bail!("dot operator can only be used with identifiers")
        };
        let indexable = indexable_and_index.0.evaluate(variables)?;

        if indexable.is_dict() {
            let f = {
                let borrowed_f = indexable.index(index)?;
                let Variant::Func(f) = &*borrowed_f else {
                    return Self::evaluate_index(variables, indexable_and_index);
                };
                if !f.is_method() {
                    return Self::evaluate_index(variables, indexable_and_index);
                }
                f.clone()
            };

            let mut body = Vec::with_capacity(f.body.len() + 1);
            body.push(Expression::Declaration {
                name: "self".into(),
                value: Box::new(Expression::Value(indexable.into_owned())),
            });

            body.extend_from_slice(f.body.as_ref());
            let new_function = Variant::func("", f.arg_names.to_vec(), body);

            Ok(Cow::Owned(new_function))
        } else if matches!(index, Variant::ShortStr(_, _) | Variant::Str(_)) {
            let id = index.as_bstr().unwrap().to_str_lossy();
            let Ok(f) = variables.get_method(id.as_ref()) else {
                return Self::evaluate_index(variables, indexable_and_index);
            };
            if !f.is_method() {
                return Self::evaluate_index(variables, indexable_and_index);
            }
            let name = f.name.clone();
            let indexable_owned = indexable.into_owned();
            let new_function = Variant::native_fn(name.as_deref(), move |a, memory| {
                let mut args = Vec::with_capacity(a.len() + 1);
                args.push(indexable_owned.clone());
                args.extend(a.iter().cloned());
                f.call(&args, memory)
            });
            Ok(Cow::Owned(new_function))
        } else {
            bail!("dot operator can only be used with identifiers")
        }
    }

    fn evaluate_index_assign<'a>(
        variables: &mut Memory,
        (indexable, index, value): &'a (Expression, Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let mut indexable = indexable.evaluate(variables)?;
        *indexable.to_mut().index_mut(&*index.evaluate(variables)?)? =
            value.evaluate(variables)?.into_owned();
        Ok(Cow::Owned(Variant::None))
    }

    fn evaluate_declaration<'a>(
        variables: &mut Memory,
        name: &str,
        value: &'a Expression,
    ) -> Result<Cow<'a, Variant>> {
        let computed_value = value.evaluate(variables)?;
        variables.set(name, computed_value.into_owned());
        Ok(Cow::Owned(Variant::None))
    }

    fn evaluate_while<'a>(
        variables: &mut Memory,
        (condition, body): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        variables.push_empty_context();
        let mut last = Cow::Owned(Variant::None);
        while condition.evaluate(variables)?.is_true()? {
            last = Cow::Owned(body.evaluate(variables)?.into_owned());
        }
        variables.pop_context();
        Ok(last)
    }

    fn evaluate_for<'a>(
        variables: &mut Memory,
        i_name: &str,
        (iterable, body): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let iterable = iterable.evaluate(variables)?.into_owned().into_iterator()?;
        let mut iterable = iterable;
        let Variant::Iterator(iterator) = &mut iterable else {
            bail!("For loop expects an iterator")
        };
        variables.push_empty_context();
        let mut last = Cow::Owned(Variant::None);

        for i in iterator.borrow_mut().clone().to_vec(variables) {
            variables.set(i_name, i);

            last = Cow::Owned(body.evaluate(variables)?.into_owned());
        }
        variables.pop_context();
        Ok(last)
    }

    fn evaluate_fstring<'a>(
        variables: &mut Memory,
        i: &'a [Expression],
    ) -> Result<Cow<'a, Variant>> {
        let mut result = Vec::new();
        for expr in i {
            let eval = expr.evaluate(variables)?;
            match eval.as_bstr() {
                Some(b) => result.extend_from_slice(b),
                None => result.extend_from_slice(eval.to_string().as_bytes()),
            }
        }
        Ok(Cow::Owned(Variant::str(result)))
    }

    pub fn value(variant: Variant) -> Expression {
        Expression::Value(variant)
    }

    fn evaluate_vector<'a>(
        variables: &mut Memory,
        i: &'a [Expression],
    ) -> Result<Cow<'a, Variant>> {
        let vec: Result<Vec<_>> = i
            .iter()
            .map(|i| i.evaluate(variables).map(|c| c.into_owned()))
            .collect();
        Ok(Cow::Owned(Variant::vec(vec?)))
    }

    fn evaluate_dictionary<'a>(
        variables: &mut Memory,
        i: &'a [(Expression, Expression)],
    ) -> Result<Cow<'a, Variant>> {
        let vec: Result<Vec<_>> = i
            .iter()
            .map(|(k, v)| {
                Ok((
                    k.evaluate(variables)?.into_owned(),
                    v.evaluate(variables)?.into_owned(),
                ))
            })
            .collect();
        Ok(Cow::Owned(Variant::dict(&vec?)))
    }

    fn evaluate_in<'a>(
        variables: &mut Memory,
        (a, b): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let lhs = a.evaluate(variables)?;
        let rhs = b.evaluate(variables)?;
        let result = match (&*lhs, &*rhs) {
            (a @ Variant::ShortStr(_, _) | a @ Variant::Str(_), b @ Variant::ShortStr(_, _) | b @ Variant::Str(_)) => {
                let sl_bstr = a.as_bstr().unwrap();
                let sr_bstr = b.as_bstr().unwrap();
                sr_bstr.contains_str(sl_bstr)
            },
            (_, Variant::Str(_)) =>  bail!("When the in operator is used to search for substrings, the left operand must be a string"),
            (lhs, Variant::Dict(d) )=> d.borrow().contains_key(&*lhs),
            (lhs, Variant::Vec(v)) => v.borrow().contains(&*lhs),
            _ => bail!("in operator can only be used with strings, dictionaries or vectors"),
        };
        Ok(Cow::Owned(Variant::Bool(result)))
    }

    // fn destructure_checks(
    //     variables: &mut Memory,
    //     names: &[String],
    //     value: &Expression,
    // ) -> Result<impl Iterator<Item = Variant>> {
    //     let Variant::Vec(vec) = value.evaluate(variables)? else {
    //         bail!("Cannot destructure {value} into {names:?}")
    //     };
    //     let vec2 = vec.clone();
    //     let vec3 = vec2.borrow();
    //     if vec3.len() != names.len() {
    //         bail!("Expected {} values, got {}", names.len(), vec3.len())
    //     }
    //     Ok(vec3.iter().cloned())
    // }

    fn _evaluate_destructure_vec_assign<'a>(
        variables: &mut Memory,
        names: &[String],
        value: &Expression,
    ) -> Result<Cow<'a, Variant>> {
        let vec = match value.evaluate(variables)? {
            Cow::Owned(Variant::Vec(vec)) => vec.clone(),
            Cow::Borrowed(Variant::Vec(vec)) => vec.clone(),
            _ => bail!("Cannot destructure {value} into {names:?}"),
        };
        let vec: &Vec<Variant> = &*vec.borrow();
        if vec.len() != names.len() {
            bail!("Expected {} values, got {}", names.len(), vec.len())
        }
        for (name, value) in names.iter().zip(vec) {
            variables.set(name, value.clone());
        }
        Ok(Cow::Owned(Variant::None))
    }

    fn _evaluate_destructure_dict_assign<'a>(
        variables: &mut Memory,
        names: &[String],
        value: &Expression,
    ) -> Result<Cow<'a, Variant>> {
        let dict = match value.evaluate(variables)? {
            Cow::Owned(Variant::Dict(dict)) => dict.clone(),
            Cow::Borrowed(Variant::Dict(dict)) => dict.clone(),
            _ => bail!("Cannot destructure {value} into {names:?}"),
        };
        let dict: &Dictionary = &*dict.borrow();
        if dict.len() != names.len() {
            bail!("Expected {} values, got {}", names.len(), dict.len())
        }

        for (name, (_key, value)) in names.iter().zip(dict) {
            if dict.contains_key(&Variant::str(name.as_str())) {
                variables.set(name, value.clone());
            } else {
                bail!("Key {name} not found in dictionary {dict:?}")
            }
        }
        Ok(Cow::Owned(Variant::None))
    }

    fn _evaluate_destructure_vec_for<'a>(
        variables: &mut Memory,
        names: &[String],
        (iterable, body): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let iterable = iterable.evaluate(variables)?.into_owned().into_iterator()?;
        let mut iterable = iterable;
        let Variant::Iterator(iterator) = &mut iterable else {
            bail!("For loop expects an iterator")
        };
        variables.push_empty_context();
        let mut last = Cow::Owned(Variant::None);

        for i in iterator.borrow_mut().clone().to_vec(variables) {
            let Variant::Vec(vec) = i else {
                bail!("Cannot destructure {i} into {names:?}")
            };
            let vec = &*vec.borrow();
            if vec.len() != names.len() {
                bail!("Expected {} values, got {}", names.len(), vec.len())
            }
            for (name, value) in names.iter().zip(vec) {
                variables.set(name, value.clone());
            }

            last = body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(last)
    }

    fn _evaluate_destructure_dict_for<'a>(
        variables: &mut Memory,
        names: &[String],
        (iterable, body): &'a (Expression, Expression),
    ) -> Result<Cow<'a, Variant>> {
        let iterable = iterable.evaluate(variables)?.into_owned().into_iterator()?;
        let mut iterable = iterable;
        let Variant::Iterator(iterator) = &mut iterable else {
            bail!("For loop expects an iterator")
        };
        variables.push_empty_context();
        let mut last = Cow::Owned(Variant::None);

        for i in iterator.borrow_mut().clone().to_vec(variables) {
            let Variant::Dict(dict) = i else {
                bail!("Cannot destructure {i} into {names:?}")
            };
            let dict = &*dict.borrow();
            if dict.len() != names.len() {
                bail!("Expected {} values, got {}", names.len(), dict.len())
            }

            for (name, (_key, value)) in names.iter().zip(dict) {
                if dict.contains_key(&Variant::str(name.as_str())) {
                    variables.set(name, value.clone());
                } else {
                    bail!("Key {name} not found in dictionary {dict:?}")
                }
            }

            last = body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(last)
    }

    pub fn evaluate<'a>(&'a self, variables: &mut Memory) -> Result<Cow<'a, Variant>> {
        match self {
            Expression::Value(v) => Ok(Cow::Borrowed(v)),
            Expression::Identifier(i) => Self::evaluate_identifier(variables, i),
            Expression::FunctionCall {
                function,
                arguments,
            } => Self::evaluate_function_call(variables, function, arguments),
            Expression::Mul(i) => Self::apply_binary_exp(variables, i, Variant::mul),
            Expression::Div(i) => Self::apply_binary_exp(variables, i, Variant::div),
            Expression::Rem(i) => Self::apply_binary_exp(variables, i, Variant::rem),
            Expression::Add(i) => Self::apply_binary_exp(variables, i, Variant::add),
            Expression::Sub(i) => Self::apply_binary_exp(variables, i, Variant::sub),
            Expression::Eq(i) => Self::apply_logical_exp(variables, i, <Variant as PartialEq>::eq),
            Expression::NotEq(i) => {
                Self::apply_logical_exp(variables, i, <Variant as PartialEq>::ne)
            }
            Expression::Gt(i) => Self::apply_logical_exp(variables, i, <Variant as PartialOrd>::gt),
            Expression::Lt(i) => Self::apply_logical_exp(variables, i, <Variant as PartialOrd>::lt),
            Expression::Gtoe(i) => {
                Self::apply_logical_exp(variables, i, <Variant as PartialOrd>::ge)
            }
            Expression::Ltoe(i) => {
                Self::apply_logical_exp(variables, i, <Variant as PartialOrd>::le)
            }
            Expression::And(i) => Self::apply_binary_exp(variables, i, Variant::and),
            Expression::Or(i) => Self::apply_binary_exp(variables, i, Variant::or),
            Expression::Neg(i) => Self::apply_unary_exp(variables, i, Variant::neg),
            Expression::Not(i) => Self::apply_unary_exp(variables, i, Variant::not),
            Expression::Block(i) => Self::evaluate_block(variables, i),
            Expression::ExprSequence(i) => Self::evaluate_expr_sequence(variables, i),
            Expression::Conditional(i) => Self::evaluate_conditional(variables, i),
            Expression::Index(i) => Self::evaluate_index(variables, i),
            Expression::IndexAssign(i) => Self::evaluate_index_assign(variables, i),
            Expression::Dot(d) => Self::evaluate_dot(variables, d),
            Expression::Declaration { name, value } => {
                Self::evaluate_declaration(variables, name, value)
            }
            Expression::While(i) => Self::evaluate_while(variables, i),
            Expression::For {
                i_name,
                iterable_and_body,
            } => Self::evaluate_for(variables, i_name, iterable_and_body),
            Expression::Fstring(i) => Self::evaluate_fstring(variables, i),
            Expression::Dictionary(i) => Self::evaluate_dictionary(variables, i),
            Expression::Vec(i) => Self::evaluate_vector(variables, i),
            Expression::FunctionDeclaration { name, function } => {
                variables.set(name, function.clone());
                Ok(Cow::Owned(Variant::None))
            }
            Expression::In(i) => Self::evaluate_in(variables, i),
            Expression::DestructureVecAssign { names: _, value: _ } => todo!(),
            Expression::DestructureDictAssign { names: _, value: _ } => todo!(),
            Expression::DestructureVecFor {
                names: _,
                iterable_and_body: _,
            } => todo!(),
            Expression::DestructureDictFor {
                names: _,
                iterable_and_body: _,
            } => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn size_of_expression() {
        assert_eq!(std::mem::size_of::<Expression>(), 40)
    }
    #[test]
    fn test_mul() {
        let mut variables = Memory::new();
        let expr = Expression::Mul(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(2)
        );
    }

    #[test]
    fn test_div() {
        let mut variables = Memory::new();
        let expr = Expression::Div(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Float(0.5)
        );
    }

    #[test]
    fn test_rem() {
        let mut variables = Memory::new();
        let expr = Expression::Rem(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));

        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(1)
        );
    }

    #[test]
    fn test_add() {
        let mut variables = Memory::new();
        let expr = Expression::Add(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(3)
        );
    }

    #[test]
    fn test_sub() {
        let mut variables = Memory::new();
        let expr = Expression::Sub(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(-1)
        );
    }

    #[test]
    fn test_eq() {
        let mut variables = Memory::new();
        let expr = Expression::Eq(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(false)
        );
    }

    #[test]
    fn test_not_eq() {
        let mut variables = Memory::new();
        let expr = Expression::NotEq(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(true)
        );
    }

    #[test]
    fn test_gt() {
        let mut variables = Memory::new();
        let expr = Expression::Gt(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(false)
        );
    }

    #[test]
    fn test_lt() {
        let mut variables = Memory::new();
        let expr = Expression::Lt(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(true)
        );
    }

    #[test]
    fn test_gtoe() {
        let mut variables = Memory::new();
        let expr = Expression::Gtoe(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(false)
        );
    }

    #[test]
    fn test_ltoe() {
        let mut variables = Memory::new();
        let expr = Expression::Ltoe(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(true)
        );
    }

    #[test]
    fn test_and() {
        let mut variables = Memory::new();
        let expr = Expression::And(Box::new((
            Expression::Value(Variant::Bool(true)),
            Expression::Value(Variant::Bool(false)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(false)
        );
    }

    #[test]
    fn test_or() {
        let mut variables = Memory::new();
        let expr = Expression::Or(Box::new((
            Expression::Value(Variant::Bool(true)),
            Expression::Value(Variant::Bool(false)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(true)
        );
    }

    #[test]
    fn test_not() {
        let mut variables = Memory::new();
        let expr = Expression::Not(Box::new(Expression::Value(Variant::Bool(true))));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Bool(false)
        );
    }

    #[test]
    fn test_dict_access() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::dict(&[(Variant::Int(1), Variant::str("test"))])),
            Expression::Value(Variant::Int(1)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::str("test")
        );
    }

    #[test]
    fn test_dict_access_not_found() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::dict(&[(Variant::Int(1), Variant::str("test"))])),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Key 2 not found in dictionary {\n    1 : \"test\"\n}"
        );
    }

    #[test]
    fn test_dict_access_not_dict() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(1)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Cannot index 1"
        );
    }

    #[test]
    fn test_vec_access() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::vec(vec![Variant::Int(1)])),
            Expression::Value(Variant::Int(0)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(1)
        );
    }

    #[test]
    fn test_vec_access_not_found() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::vec(vec![Variant::Int(1)])),
            Expression::Value(Variant::Int(1)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Index 1 out of bounds"
        );
    }

    #[test]
    fn test_vec_access_not_vec() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(0)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Cannot index 1"
        );
    }

    #[test]
    fn test_fstring() {
        let mut variables = Memory::new();
        let expr = Expression::Fstring(vec![
            Expression::Value(Variant::str("test A ")),
            Expression::Div(Box::new((
                Expression::Value(Variant::Int(1)),
                Expression::Value(Variant::Int(2)),
            ))),
            Expression::Value(Variant::str(" test B ")),
            Expression::And(Box::new((
                Expression::Value(Variant::Bool(true)),
                Expression::Value(Variant::Bool(false)),
            ))),
            Expression::Value(Variant::str(" test C")),
        ]);
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::str("test A 0.5 test B false test C")
        );
    }

    #[test]
    fn test_native_function_call() {
        let mut variables = Memory::new();
        variables.set("arg", Variant::Int(1));
        let native_function =
            Expression::Value(Variant::native_fn(None, |i, _| i[0].add(&Variant::Int(2))));
        let expr = Expression::FunctionCall {
            function: Box::new(native_function),
            arguments: vec![Expression::Identifier("arg".to_string())],
        };
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(3)
        );
    }

    #[test]
    fn test_declaration() {
        let mut variables = Memory::new();
        let expr = Expression::Declaration {
            name: "arg".to_string(),
            value: Box::new(Expression::Value(Variant::Int(1))),
        };
        expr.evaluate(&mut variables).unwrap().into_owned();
        assert_eq!(&*variables.get("arg").unwrap(), &Variant::Int(1));
    }

    #[test]
    fn test_while_loop() {
        let mut variables = Memory::new();
        variables.set("i", Variant::Int(0));
        let expr = Expression::While(Box::new((
            Expression::Lt(Box::new((
                Expression::Identifier("i".to_string()),
                Expression::Value(Variant::Int(10)),
            ))),
            Expression::Declaration {
                name: "i".to_string(),
                value: Box::new(Expression::Add(Box::new((
                    Expression::Identifier("i".to_string()),
                    Expression::Value(Variant::Int(1)),
                )))),
            },
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::None
        );
        dbg!(&variables);
        assert_eq!(&*variables.get("i").unwrap(), &Variant::Int(10));
    }
    #[test]
    fn test_for_loop() {
        let mut variables = Memory::new();
        variables.set(
            "v",
            Variant::vec(vec![
                Variant::Int(0),
                Variant::Int(1),
                Variant::Int(2),
                Variant::Int(3),
            ]),
        );
        let expr = Expression::For {
            i_name: "i".to_string(),
            iterable_and_body: Box::new((
                Expression::Identifier("v".to_string()),
                Expression::FunctionCall {
                    function: Box::new(Expression::Value(Variant::native_fn(None, |i, _| {
                        println!("{:?}", i[0]);
                        Ok(Variant::None)
                    }))),
                    arguments: vec![Expression::Identifier("i".to_string())],
                },
            )),
        };

        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::None
        );
        dbg!(variables);
    }

    #[test]
    fn test_filter() {
        let mut variables = Memory::with_builtins();
        variables.set(
            "v",
            Variant::vec(vec![
                Variant::Int(0),
                Variant::Int(1),
                Variant::Int(2),
                Variant::Int(3),
            ]),
        );

        variables.set(
            "is_even",
            Variant::native_fn(None, |i, _| {
                Ok(Variant::Bool(
                    i[0].rem(&Variant::Int(2)).unwrap() == Variant::Int(0),
                ))
            }),
        );

        let expr = Expression::ExprSequence(vec![Expression::FunctionCall {
            function: Box::new(Expression::Dot(Box::new((
                Expression::FunctionCall {
                    function: Box::new(Expression::Dot(Box::new((
                        Expression::Identifier("v".to_string()),
                        Expression::Value(Variant::str("filter")),
                    )))),
                    arguments: vec![Expression::Identifier("is_even".to_string())],
                },
                Expression::Value(Variant::str("to_vec")),
            )))),
            arguments: vec![],
        }]);

        dbg!(&variables);
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::vec(vec![Variant::Int(0), Variant::Int(2),])
        );
    }

    #[test]
    fn test_if() {
        let mut variables = Memory::new();
        variables.set("v", Variant::Int(0));
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::Value(Variant::Int(0)),
            ))),
            Expression::Value(Variant::Int(1)),
            Some(Expression::Value(Variant::Int(2))),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(1)
        );
    }

    #[test]
    fn test_if_else() {
        let mut variables = Memory::new();
        variables.set("v", Variant::Int(0));
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::Value(Variant::Int(1)),
            ))),
            Expression::Value(Variant::Int(1)),
            Some(Expression::Value(Variant::Int(2))),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(2)
        );
    }

    #[test]
    fn test_function_call() {
        let mut variables = Memory::new();
        variables.set(
            "add_1",
            Variant::anonymous_func(
                vec![("i".into(), None)],
                vec![Expression::Add(Box::new((
                    Expression::Identifier("i".to_string()),
                    Expression::Value(Variant::Int(1)),
                )))],
            ),
        );
        let expr = Expression::FunctionCall {
            function: Box::new(Expression::Identifier("add_1".to_string())),
            arguments: vec![Expression::Value(Variant::Int(1))],
        };
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(2)
        );
    }

    #[test]
    fn test_scope() {
        let mut variables = Memory::new();

        let expr = Expression::Block(vec![
            Expression::Declaration {
                name: "i".to_string(),
                value: Box::new(Expression::Value(Variant::Int(1))),
            },
            Expression::Declaration {
                name: "j".to_string(),
                value: Box::new(Expression::Value(Variant::Int(2))),
            },
            Expression::Add(Box::new((
                Expression::Identifier("i".to_string()),
                Expression::Identifier("j".to_string()),
            ))),
        ]);
        assert_eq!(
            expr.evaluate(&mut variables).unwrap().into_owned(),
            Variant::Int(3)
        );
    }
}
