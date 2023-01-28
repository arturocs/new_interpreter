use crate::{memory::Memory, variant::Variant};
use anyhow::{anyhow, Result};

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

    // First expression -> condition, second -> if body, third -> else body
    Conditional(Box<(Expression, Expression, Option<Expression>)>),
    // First expression -> indexable, second -> index
    Index(Box<(Expression, Expression)>),
    // First expression -> indexable, second -> index, third -> value
    IndexAssign(Box<(Expression, Expression, Expression)>),

    Fstring(Vec<Expression>),

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
        variables.get(i).cloned()
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
                Ok(f.call(&evaluated_args))
            }
            Variant::Func(f) => {
                let evaluated_args: Result<Vec<_>> =
                    arguments.iter().map(|e| e.evaluate(variables)).collect();
                f.call(&evaluated_args?, variables)
            }
            a => Err(anyhow::anyhow!("{a:?} is not a function")),
        }
    }

    fn evaluate_block(variables: &mut Memory, statements: &[Expression]) -> Result<Variant> {
        variables.push_empty_context();
        let result = statements
            .iter()
            .map(|e| e.evaluate(variables))
            .last()
            .ok_or_else(|| anyhow!("No statements in scope"))?;
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

    fn evaluate_index_assign(
        variables: &mut Memory,
        (indexable, index, value): &(Expression, Expression, Expression),
    ) -> Result<Variant> {
        *indexable
            .evaluate(variables)?
            .index_mut(&index.evaluate(variables)?)? = value.evaluate(variables)?;
        Ok(Variant::error("Statement does not return a value"))
    }

    fn evaluate_declaration(
        variables: &mut Memory,
        name: &str,
        value: &Expression,
    ) -> Result<Variant> {
        let computed_value = value.evaluate(variables)?;
        variables.set(name, computed_value)?;
        Ok(Variant::error("Statement does not return a value"))
    }

    fn evaluate_while(
        variables: &mut Memory,
        (condition, body): &(Expression, Expression),
    ) -> Result<Variant> {
        variables.push_empty_context();
        while condition.evaluate(variables)?.is_true()? {
            body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(Variant::error("While loop does not return a value"))
    }

    fn evaluate_for(
        variables: &mut Memory,
        i_name: &str,
        (iterable, body): &(Expression, Expression),
    ) -> Result<Variant> {
        let iterable = iterable.evaluate(variables)?.into_iterator()?;
        let mut iterable = iterable;
        let iterator = match &mut iterable {
            Variant::Iterator(i) => i,
            _ => return Err(anyhow!("For loop expects an iterator")),
        };
        variables.push_empty_context();
        for i in iterator {
            variables.set(i_name, i)?;

            body.evaluate(variables)?;
        }
        variables.pop_context();
        Ok(Variant::error("For loop does not return a value"))
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
        Ok(Variant::Vec(vec?))
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
            Expression::Eq(i) => Self::apply_logical_exp(variables, i, Variant::eq),
            Expression::NotEq(i) => Self::apply_logical_exp(variables, i, Variant::ne),
            Expression::Gt(i) => Self::apply_logical_exp(variables, i, Variant::gt),
            Expression::Lt(i) => Self::apply_logical_exp(variables, i, Variant::lt),
            Expression::Gtoe(i) => Self::apply_logical_exp(variables, i, Variant::ge),
            Expression::Ltoe(i) => Self::apply_logical_exp(variables, i, Variant::le),
            Expression::And(i) => Self::apply_binary_exp(variables, i, Variant::and),
            Expression::Or(i) => Self::apply_binary_exp(variables, i, Variant::or),
            Expression::Neg(i) => Self::apply_unary_exp(variables, i, Variant::neg),
            Expression::Not(i) => Self::apply_unary_exp(variables, i, Variant::not),
            Expression::Block(i) => Self::evaluate_block(variables, i),
            Expression::Conditional(i) => Self::evaluate_conditional(variables, i),
            Expression::Index(i) => Self::evaluate_index(variables, i),
            Expression::IndexAssign(i) => Self::evaluate_index_assign(variables, i),
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
            // _ => todo!(),
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
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
    }

    #[test]
    fn test_div() {
        let mut variables = Memory::new();
        let expr = Expression::Div(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Float(0.5));
    }

    #[test]
    fn test_rem() {
        let mut variables = Memory::new();
        let expr = Expression::Rem(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
    }

    #[test]
    fn test_add() {
        let mut variables = Memory::new();
        let expr = Expression::Add(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(3));
    }

    #[test]
    fn test_sub() {
        let mut variables = Memory::new();
        let expr = Expression::Sub(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(-1));
    }

    #[test]
    fn test_eq() {
        let mut variables = Memory::new();
        let expr = Expression::Eq(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_not_eq() {
        let mut variables = Memory::new();
        let expr = Expression::NotEq(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_gt() {
        let mut variables = Memory::new();
        let expr = Expression::Gt(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_lt() {
        let mut variables = Memory::new();
        let expr = Expression::Lt(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_gtoe() {
        let mut variables = Memory::new();
        let expr = Expression::Gtoe(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_ltoe() {
        let mut variables = Memory::new();
        let expr = Expression::Ltoe(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_and() {
        let mut variables = Memory::new();
        let expr = Expression::And(Box::new((
            Expression::value(Variant::Bool(true)),
            Expression::value(Variant::Bool(false)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_or() {
        let mut variables = Memory::new();
        let expr = Expression::Or(Box::new((
            Expression::value(Variant::Bool(true)),
            Expression::value(Variant::Bool(false)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn test_not() {
        let mut variables = Memory::new();
        let expr = Expression::Not(Box::new(Expression::value(Variant::Bool(true))));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Bool(false));
    }

    #[test]
    fn test_dict_access() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::value(Variant::dict(&[(Variant::Int(1), Variant::str("test"))])),
            Expression::value(Variant::Int(1)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::str("test"));
    }

    #[test]
    fn test_dict_access_not_found() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::value(Variant::dict(&[(Variant::Int(1), Variant::str("test"))])),
            Expression::value(Variant::Int(2)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Key not found in dictionary"
        );
    }

    #[test]
    fn test_dict_access_not_dict() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(1)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Cannot index Int(1)"
        );
    }

    #[test]
    fn test_vec_access() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::value(Variant::Vec(vec![Variant::Int(1)])),
            Expression::value(Variant::Int(0)),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
    }

    #[test]
    fn test_vec_access_not_found() {
        let mut variables = Memory::new();
        let expr = Expression::Index(Box::new((
            Expression::value(Variant::Vec(vec![Variant::Int(1)])),
            Expression::value(Variant::Int(1)),
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
            Expression::value(Variant::Int(1)),
            Expression::value(Variant::Int(0)),
        )));
        assert_eq!(
            expr.evaluate(&mut variables).err().unwrap().to_string(),
            "Cannot index Int(1)"
        );
    }

    #[test]
    fn test_fstring() {
        let mut variables = Memory::new();
        let expr = Expression::Fstring(vec![
            Expression::value(Variant::str("test A ")),
            Expression::Div(Box::new((
                Expression::value(Variant::Int(1)),
                Expression::value(Variant::Int(2)),
            ))),
            Expression::value(Variant::str(" test B ")),
            Expression::And(Box::new((
                Expression::value(Variant::Bool(true)),
                Expression::value(Variant::Bool(false)),
            ))),
            Expression::value(Variant::str(" test C")),
        ]);
        assert_eq!(
            expr.evaluate(&mut variables).unwrap(),
            Variant::str("test A 0.5 test B false test C")
        );
    }

    #[test]
    fn test_native_function_call() {
        let mut variables = Memory::new();
        variables.set("arg".into(), Variant::Int(1)).unwrap();
        let native_function =
            Expression::value(Variant::native_fn(|i| i[0].add(&Variant::Int(2)).unwrap()));
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
            value: Box::new(Expression::value(Variant::Int(1))),
        };
        expr.evaluate(&mut variables).unwrap();
        assert_eq!(variables.get("arg").unwrap(), &Variant::Int(1));
    }

    #[test]
    fn test_while_loop() {
        let mut variables = Memory::new();
        variables.set("i".into(), Variant::Int(0)).unwrap();
        let expr = Expression::While(Box::new((
            Expression::Lt(Box::new((
                Expression::Identifier("i".to_string()),
                Expression::value(Variant::Int(10)),
            ))),
            Expression::Declaration {
                name: "i".to_string(),
                value: Box::new(Expression::Add(Box::new((
                    Expression::Identifier("i".to_string()),
                    Expression::value(Variant::Int(1)),
                )))),
            },
        )));
        assert_eq!(
            expr.evaluate(&mut variables).unwrap(),
            Variant::error("While loop does not return a value")
        );
        dbg!(&variables);
        assert_eq!(variables.get("i").cloned().unwrap(), Variant::Int(10));
    }
    #[test]
    fn test_for_loop() {
        let mut variables = Memory::new();
        variables
            .set(
                "v".into(),
                Variant::Vec(vec![
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
                    function: Box::new(Expression::value(Variant::native_fn(|i| {
                        println!("{:?}", i[0]);
                        Variant::error("No return value")
                    }))),
                    arguments: vec![Expression::Identifier("i".to_string())],
                },
            )),
        };

        assert_eq!(
            expr.evaluate(&mut variables).unwrap(),
            Variant::error("For loop does not return a value")
        );
        dbg!(variables);
    }

    #[test]
    fn test_filter() {
        let mut variables = Memory::new();
        variables
            .set(
                "v".into(),
                Variant::Vec(vec![
                    Variant::Int(0),
                    Variant::Int(1),
                    Variant::Int(2),
                    Variant::Int(3),
                ]),
            )
            .unwrap();
        variables
            .set(
                "filter".into(),
                Variant::native_fn(|i| {
                    let iter = &i[0];
                    let func = &i[1];
                    iter.clone()
                        .filter(func.clone())
                        .unwrap()
                        .into_vec()
                        .unwrap()
                }),
            )
            .unwrap();

        variables
            .set(
                "is_even".into(),
                Variant::native_fn(|i| {
                    Variant::Bool(i[0].rem(&Variant::Int(2)).unwrap() == Variant::Int(0))
                }),
            )
            .unwrap();
        let expr = Expression::FunctionCall {
            function: Box::new(Expression::Identifier("filter".to_string())),
            arguments: vec![
                Expression::Identifier("v".to_string()),
                Expression::Identifier("is_even".to_string()),
            ],
        };
        dbg!(&variables);
        assert_eq!(
            expr.evaluate(&mut variables).unwrap(),
            Variant::Vec(vec![Variant::Int(0), Variant::Int(2),])
        );
    }

    #[test]
    fn test_if() {
        let mut variables = Memory::new();
        variables.set("v".into(), Variant::Int(0)).unwrap();
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::value(Variant::Int(0)),
            ))),
            Expression::value(Variant::Int(1)),
            Some(Expression::value(Variant::Int(2))),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(1));
    }

    #[test]
    fn test_if_else() {
        let mut variables = Memory::new();
        variables.set("v".into(), Variant::Int(0)).unwrap();
        let expr = Expression::Conditional(Box::new((
            Expression::Eq(Box::new((
                Expression::Identifier("v".to_string()),
                Expression::value(Variant::Int(1)),
            ))),
            Expression::value(Variant::Int(1)),
            Some(Expression::value(Variant::Int(2))),
        )));
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
    }

    #[test]
    fn test_function_call() {
        let mut variables = Memory::new();
        variables
            .set(
                "add_1".into(),
                Variant::func(
                    vec!["i".into()],
                    vec![Expression::Add(Box::new((
                        Expression::Identifier("i".to_string()),
                        Expression::value(Variant::Int(1)),
                    )))],
                ),
            )
            .unwrap();
        let expr = Expression::FunctionCall {
            function: Box::new(Expression::Identifier("add_1".to_string())),
            arguments: vec![Expression::value(Variant::Int(1))],
        };
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(2));
    }

    /* #[test]
       fn test_function_call_by_reference() {
           let mut variables = Memory::new();
           variables.set(
               "set_arg_to_1".to_string(),
               Variant::func(
                   vec!["i".to_string()],
                   vec![Expression::Declaration {
                       name: "i".to_string(),
                       value: Box::new(Expression::value(Variant::Int(1))),
                   }],
               ),
           );
           variables.set("j".to_string(), Variant::Int(0));
           dbg!(&variables);
           let expr = Expression::FunctionCall {
               function: Box::new(Expression::Identifier("set_arg_to_1".to_string())),
               arguments: vec![Expression::Identifier("j".to_string())],
           };
           assert_eq!(
               expr.evaluate(&mut variables).unwrap(),
               Variant::error("Statement does not return a value")
           );
           dbg!(&variables);
           assert_eq!(variables.last().unwrap()["j"].clone(), Variant::Int(1));
       }
    */
    #[test]
    fn test_scope() {
        let mut variables = Memory::new();

        let expr = Expression::Block(vec![
            Expression::Declaration {
                name: "i".to_string(),
                value: Box::new(Expression::value(Variant::Int(1))),
            },
            Expression::Declaration {
                name: "j".to_string(),
                value: Box::new(Expression::value(Variant::Int(2))),
            },
            Expression::Add(Box::new((
                Expression::Identifier("i".to_string()),
                Expression::Identifier("j".to_string()),
            ))),
        ]);
        assert_eq!(expr.evaluate(&mut variables).unwrap(), Variant::Int(3));
    }
}
