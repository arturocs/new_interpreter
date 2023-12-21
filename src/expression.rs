use crate::{memory::Memory, variant::Variant};
use anyhow::{anyhow, bail, Context, Result};
use bstr::ByteSlice;
use itertools::Itertools;
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
        }
    }
}

impl Expression {
    fn apply_binary_exp(
        variables: &mut Memory,
        (a, b): &(Expression, Expression),
        expr: fn(&Variant, &Variant) -> Result<Variant>,
    ) -> Result<Variant> {
        let lhs = a.evaluate(variables)?;
        let rhs = b.evaluate(variables)?;
        expr(&lhs, &rhs)
    }

    fn apply_unary_exp(
        variables: &mut Memory,
        i: &Expression,
        expr: fn(&Variant) -> Result<Variant>,
    ) -> Result<Variant> {
        let value = i.evaluate(variables)?;
        expr(&value)
    }

    fn apply_logical_exp(
        variables: &mut Memory,
        (a, b): &(Expression, Expression),
        expr: fn(&Variant, &Variant) -> bool,
    ) -> Result<Variant> {
        let lhs = a.evaluate(variables)?;
        let rhs = b.evaluate(variables)?;
        Ok(Variant::Bool(expr(&lhs, &rhs)))
    }

    fn evaluate_identifier(variables: &mut Memory, i: &str) -> Result<Variant> {
        variables.get(i).map(|i| i.clone())
    }

    fn evaluate_function_call(
        variables: &mut Memory,
        function: &Expression,
        arguments: &[Expression],
    ) -> Result<Variant> {
        match function.evaluate(variables)? {
            Variant::NativeFunc(f) => {
                let evaluated_args = arguments
                    .iter()
                    .map(|e| e.evaluate(variables))
                    .collect::<Result<Vec<_>>>()?;
                Ok(f.call(&evaluated_args, variables))
            }
            Variant::Func(f) => {
                let evaluated_args: Result<Vec<_>> =
                    arguments.iter().map(|e| e.evaluate(variables)).collect();
                f.call(&evaluated_args?, variables)
            }
            a => bail!("{a} is not a function"),
        }
    }

    pub fn evaluate_expr_sequence(
        variables: &mut Memory,
        statements: &[Expression],
    ) -> Result<Variant> {
        let results: Result<Vec<_>> = statements
            .iter()
            .map(|e| match e.evaluate(variables) {
                Ok(Variant::Error(e)) => Err(anyhow!("{}", e.trim_start_matches("Error: "))),
                a => a,
            })
            .collect();
        let results = results?;
        results.last().context("No statements in scope").cloned()
    }

    fn evaluate_block(variables: &mut Memory, statements: &[Expression]) -> Result<Variant> {
        variables.push_empty_context();
        let result = Self::evaluate_expr_sequence(variables, statements);
        variables.pop_context();
        result
    }

    fn evaluate_conditional(
        variables: &mut Memory,
        (condition, if_body, else_body): &(Expression, Expression, Option<Expression>),
    ) -> Result<Variant> {
        if condition.evaluate(variables)? == Variant::Bool(true) {
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
            Ok(Variant::error("No else body"))
        }
    }

    fn evaluate_index(
        variables: &mut Memory,
        (indexable, index): &(Expression, Expression),
    ) -> Result<Variant> {
        indexable
            .evaluate(variables)?
            .index(&index.evaluate(variables)?)
            .map(|i| i.clone())
    }

    fn evaluate_dot(
        variables: &mut Memory,
        indexable_and_index: &(Expression, Expression),
    ) -> Result<Variant> {
        let Expression::Value(index) = &indexable_and_index.1 else {
            bail!("dot operator can only be used with identifiers")
        };
        let indexable = indexable_and_index.0.evaluate(variables)?;

        if indexable.is_dict() {
            let Variant::Func(f) = &*indexable.index(index)? else {
                return Self::evaluate_index(variables, indexable_and_index);
            };
            if !f.is_method() {
                return Self::evaluate_index(variables, indexable_and_index);
            }

            let mut body = Vec::with_capacity(f.body.len() + 1);
            body.push(Expression::Declaration {
                name: "self".into(),
                value: Box::new(Expression::Value(indexable.clone())),
            });

            body.extend_from_slice(f.body.as_ref());
            let new_function = Variant::func("", f.arg_names.to_vec(), body);

            Ok(new_function)
        } else {
            let Variant::Str(id) = index else {
                bail!("dot operator can only be used with identifiers")
            };
            let Ok(Variant::NativeFunc(f)) =
                variables.get_method(&id.to_str_lossy()).map(|i| i.clone())
            else {
                return Self::evaluate_index(variables, indexable_and_index);
            };
            if !f.is_method() {
                return Self::evaluate_index(variables, indexable_and_index);
            }

            let new_function = Variant::native_fn(None, move |a, memory| {
                let mut args = Vec::with_capacity(a.len() + 1);
                args.push(indexable.clone());
                args.extend(a.iter().cloned());
                f.call(&args, memory)
            });
            Ok(new_function)
        }
    }

    fn evaluate_index_assign(
        variables: &mut Memory,
        (indexable, index, value): &(Expression, Expression, Expression),
    ) -> Result<Variant> {
        *indexable
            .evaluate(variables)?
            .index_mut(&index.evaluate(variables)?)? = value.evaluate(variables)?;
        Ok(Variant::Unit)
    }

    fn evaluate_declaration(
        variables: &mut Memory,
        name: &str,
        value: &Expression,
    ) -> Result<Variant> {
        let computed_value = value.evaluate(variables)?;
        variables.set(name, computed_value)?;
        Ok(Variant::Unit)
    }

    fn evaluate_while(
        variables: &mut Memory,
        (condition, body): &(Expression, Expression),
    ) -> Result<Variant> {
        variables.push_empty_context();
        let mut last = Variant::Unit;
        while condition.evaluate(variables)?.is_true()? {
            last = body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(last)
    }

    fn evaluate_for(
        variables: &mut Memory,
        i_name: &str,
        (iterable, body): &(Expression, Expression),
    ) -> Result<Variant> {
        let iterable = iterable.evaluate(variables)?.into_iterator()?;
        let mut iterable = iterable;
        let Variant::Iterator(iterator) = &mut iterable else {
            bail!("For loop expects an iterator")
        };
        variables.push_empty_context();
        let mut last = Variant::Unit;

        for i in iterator.borrow_mut().clone().to_vec(variables) {
            variables.set(i_name, i)?;

            last = body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(last)
    }

    fn evaluate_fstring(variables: &mut Memory, i: &[Expression]) -> Result<Variant> {
        let s: Result<String> = i
            .iter()
            .map(|e| Ok(e.evaluate(variables)?.to_string()))
            .collect();
        Ok(Variant::str(s?))
    }

    pub fn value(variant: Variant) -> Expression {
        Expression::Value(variant)
    }

    fn evaluate_vector(variables: &mut Memory, i: &[Expression]) -> Result<Variant> {
        let vec: Result<Vec<_>> = i.iter().map(|i| i.evaluate(variables)).collect();
        Ok(Variant::vec(vec?))
    }

    fn evaluate_dictionary(
        variables: &mut Memory,
        i: &[(Expression, Expression)],
    ) -> Result<Variant> {
        let vec: Result<Vec<_>> = i
            .iter()
            .map(|(k, v)| Ok((k.evaluate(variables)?, v.evaluate(variables)?)))
            .collect();
        Ok(Variant::dict(&vec?))
    }

    pub fn evaluate(&self, variables: &mut Memory) -> Result<Variant> {
        match self {
            Expression::Value(v) => Ok(v.clone()),
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
                Self::evaluate_declaration(variables, name, &Expression::Value(function.clone()))
            }
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
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
    }

    #[test]
    fn test_div() {
        let mut variables = Memory::new();
        let expr = Expression::Div(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Float(0.5));
    }

    #[test]
    fn test_rem() {
        let mut variables = Memory::new();
        let expr = Expression::Rem(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));

        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
    }

    #[test]
    fn test_add() {
        let mut variables = Memory::new();
        let expr = Expression::Add(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(3));
    }

    #[test]
    fn test_sub() {
        let mut variables = Memory::new();
        let expr = Expression::Sub(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(-1));
    }

    #[test]
    fn test_eq() {
        let mut variables = Memory::new();
        let expr = Expression::Eq(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_not_eq() {
        let mut variables = Memory::new();
        let expr = Expression::NotEq(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_gt() {
        let mut variables = Memory::new();
        let expr = Expression::Gt(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_lt() {
        let mut variables = Memory::new();
        let expr = Expression::Lt(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_gtoe() {
        let mut variables = Memory::new();
        let expr = Expression::Gtoe(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_ltoe() {
        let mut variables = Memory::new();
        let expr = Expression::Ltoe(Box::new((
            Expression::Value(Variant::Int(1)),
            Expression::Value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_and() {
        let mut variables = Memory::new();
        let expr = Expression::And(Box::new((
            Expression::Value(Variant::Bool(true)),
            Expression::Value(Variant::Bool(false)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_or() {
        let mut variables = Memory::new();
        let expr = Expression::Or(Box::new((
            Expression::Value(Variant::Bool(true)),
            Expression::Value(Variant::Bool(false)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_not() {
        let mut variables = Memory::new();
        let expr = Expression::Not(Box::new(Expression::Value(Variant::Bool(true))));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_dict_access() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::Value(Variant::dict(&[(Variant::Int(1), Variant::str("test"))])),
            Expression::Value(Variant::Int(1)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::str("test"));
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
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
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
            expr.evaluate(&mut variables).unwrap(),
            Variant::str("test A 0.5 test B false test C")
        );
    }

    #[test]
    fn test_native_function_call() {
        let mut variables = Memory::new();
        variables.set("arg", Variant::Int(1)).unwrap();
        let native_function = Expression::Value(Variant::native_fn(None, |i, _| {
            i[0].add(&Variant::Int(2)).unwrap()
        }));
        let expr = Expression::FunctionCall {
            function: Box::new(native_function),
            arguments: vec![Expression::Identifier("arg".to_string())],
        };
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(3));
    }

    #[test]
    fn test_declaration() {
        let mut variables = Memory::new();
        let expr = Expression::Declaration {
            name: "arg".to_string(),
            value: Box::new(Expression::Value(Variant::Int(1))),
        };
        expr.evaluate(&mut variables).unwrap();
        assert_eq!(&*variables.get("arg").unwrap(), &Variant::Int(1));
    }

    #[test]
    fn test_while_loop() {
        let mut variables = Memory::new();
        variables.set("i", Variant::Int(0)).unwrap();
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
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Unit);
        dbg!(&variables);
        assert_eq!(&*variables.get("i").unwrap(), &Variant::Int(10));
    }
    #[test]
    fn test_for_loop() {
        let mut variables = Memory::new();
        variables
            .set(
                "v",
                Variant::vec(vec![
                    Variant::Int(0),
                    Variant::Int(1),
                    Variant::Int(2),
                    Variant::Int(3),
                ]),
            )
            .unwrap();
        let expr = Expression::For {
            i_name: "i".to_string(),
            iterable_and_body: Box::new((
                Expression::Identifier("v".to_string()),
                Expression::FunctionCall {
                    function: Box::new(Expression::Value(Variant::native_fn(None, |i, _| {
                        println!("{:?}", i[0]);
                        Variant::Unit
                    }))),
                    arguments: vec![Expression::Identifier("i".to_string())],
                },
            )),
        };

        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Unit);
        dbg!(variables);
    }

    #[test]
    fn test_filter() {
        let mut variables = Memory::with_builtins();
        variables
            .set(
                "v",
                Variant::vec(vec![
                    Variant::Int(0),
                    Variant::Int(1),
                    Variant::Int(2),
                    Variant::Int(3),
                ]),
            )
            .unwrap();

        variables
            .set(
                "is_even",
                Variant::native_fn(None, |i, _| {
                    Variant::Bool(i[0].rem(&Variant::Int(2)).unwrap() == Variant::Int(0))
                }),
            )
            .unwrap();

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
            expr.evaluate(&mut variables).unwrap(),
            Variant::vec(vec![Variant::Int(0), Variant::Int(2),])
        );
    }

    #[test]
    fn test_if() {
        let mut variables = Memory::new();
        variables.set("v", Variant::Int(0)).unwrap();
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::Value(Variant::Int(0)),
            ))),
            Expression::Value(Variant::Int(1)),
            Some(Expression::Value(Variant::Int(2))),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
    }

    #[test]
    fn test_if_else() {
        let mut variables = Memory::new();
        variables.set("v", Variant::Int(0)).unwrap();
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::Value(Variant::Int(1)),
            ))),
            Expression::Value(Variant::Int(1)),
            Some(Expression::Value(Variant::Int(2))),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
    }

    #[test]
    fn test_function_call() {
        let mut variables = Memory::new();
        variables
            .set(
                "add_1",
                Variant::anonymous_func(
                    vec![("i".into(), None)],
                    vec![Expression::Add(Box::new((
                        Expression::Identifier("i".to_string()),
                        Expression::Value(Variant::Int(1)),
                    )))],
                ),
            )
            .unwrap();
        let expr = Expression::FunctionCall {
            function: Box::new(Expression::Identifier("add_1".to_string())),
            arguments: vec![Expression::Value(Variant::Int(1))],
        };
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
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
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(3));
    }
}
