use crate::{expression::Expression, variant::Variant};

peg::parser!(pub grammar expr_parser() for str {
    rule _() = [' ' | '\t']*

    rule __() = [' ' | '\t' | '\n'| '\r']*

    rule value_separator() = __ "," __

    rule expr_separator() = _ [';' | '\n'| '\r']+ _

    rule number() -> Expression
        = n:$("-"? int() frac()? exp()?) {?
            let int = n.parse().map(|i| Expression::Value(Variant::Int(i))).or(Err(""));
            if int.is_ok(){
                return int
            }
            n.parse().map(|i| Expression::Value(Variant::Float(i))).or(Err("Can't parse float"))
        }

    rule int() = ['0'..='9']+

    rule exp() = ("e" / "E") ("-" / "+")? ['0'..='9']*<1,>

    rule frac() = "." ['0'..='9']*<1,>

    rule true_() -> Expression = "true" {Expression::Value(Variant::Bool(true))}

    rule false_() -> Expression = "false" {Expression::Value(Variant::Bool(false))}

    rule string() -> Expression
        = s:$("\"" (!"\"" [_])* "\"") { Expression::Value(Variant::str(&s[1..s.len()-1])) }

    rule identifier() -> Expression
        = i:$( ([ 'a'..='z' | 'A'..='Z' | '_' ]['a'..='z' | 'A'..='Z' | '0'..='9' | '_' ]*) ) {
            Expression::Identifier(i.to_string())
        }

    rule vec() -> Expression
        = "[" _ v:(expression() ** value_separator()) _ "]" {Expression::Vec(v)}

    rule member() -> (Expression, Expression)
        = k:expression() _ ":" _ v:expression() {
            if let Expression::Identifier(i) = k {
                (Expression::Value(Variant::str(i)), v)
            } else{
                (k, v)
            }
        }

    rule dict() -> Expression = "{" __ o:(member() ** value_separator()) __ "}"  {Expression::Dictionary(o)}

    rule fstring_expression() -> Expression  = "{" _ e:expression() _ "}"{e}

    rule fstring_chars() -> Expression = s:$((!"\"" [_])) { Expression::Value(Variant::str(s))}

    rule fstring() -> Expression
        = "f\"" e:(fstring_expression() /fstring_chars())* "\"" {
            Expression::Fstring(e)
        }

    rule block() -> Expression
        =  "{" __ v:(expression() ++ (expr_separator()*)) __ "}" {
            Expression::Block(v)
        }

    rule while_() -> Expression
        = "while" _ e:expression() _ b:block(){
            Expression::While(Box::new((e, b)))
        }

    rule for_() -> Expression
        = "for" _ i:$identifier() _ "in" _ it:expression() _ b:block(){
            Expression::For{ i_name:i.into(), iterable_and_body: Box::new((it,b))}
        }

    rule if_() -> Expression
        = "if" _ c:expression() _ b1:block() {
            Expression::Conditional(Box::new((c,b1,None)))
        }

    rule if_else() -> Expression
        = "if" _ c:expression() _ b1:block() _ "else" _ b2:block() {
            Expression::Conditional(Box::new((c,b1,Some(b2))))
        }

    rule anonymous_function() -> Expression
        = "|" _ a:(identifier() ** value_separator()) _ "|" _ b:(expression()/block()) {
            let args: Vec<_> = a
            .into_iter()
            .map(|i| {
                if let Expression::Identifier(id) = i {
                    id.into()
                } else {
                    unreachable!()
                }
            })
            .collect();
            let body = if let Expression::Block(bl) = b { bl } else { vec![b] };
            Expression::Value(Variant::anonymous_func(args, body))
        }

    rule function_declaration() -> Expression
        = "fn" _ i:$identifier() "(" _ a:(identifier() ** value_separator()) _ ")" _ b:block() {
            let args: Vec<_> = a
            .into_iter()
            .map(|i| {
                if let Expression::Identifier(id) = i {
                    id.into()
                } else {
                    unreachable!()
                }
            })
            .collect();
            let body = if let Expression::Block(bl) = b { bl } else { vec![b] };
            Expression::FunctionDeclaration { name:i.into(), function: Variant::func(i,args, body) }
        }

    pub rule expression() -> Expression = precedence!{

        i:$identifier() _ "=" _ v:@ {
            Expression::Declaration{
                name:i.into(),
                value:Box::new(v)
            }
        }

        e:(@) "["  _ i:expression() _ "]" _ "=" _ v:@ {
            Expression::IndexAssign(Box::new((e,i,v)))
        }
        e:(@) "." i:$identifier() _ "=" _ v:@ {
            Expression::IndexAssign(Box::new((e,Expression::Value(Variant::str(i)),v)))
        }

        --
        x:(@) _ ("||"/"or") _ y:@ { Expression::Or(Box::new((x,y))) }
        --
        x:(@) _ ("&&"/"and") _ y:@ { Expression::And(Box::new((x,y))) }
        --
        x:(@) _ "==" _ y:@ { Expression::Eq(Box::new((x,y))) }
        x:(@) _ "!=" _ y:@ { Expression::NotEq(Box::new((x,y))) }
        --
        x:(@) _ "<" _ y:@ { Expression::Lt(Box::new((x,y))) }
        x:(@) _ ">" _ y:@ { Expression::Gt(Box::new((x,y))) }
        x:(@) _ "<=" _ y:@ { Expression::Ltoe(Box::new((x,y))) }
        x:(@) _ ">=" _ y:@ { Expression::Gtoe(Box::new((x,y))) }
        --
        x:(@) _ "+" _ y:@ { Expression::Add(Box::new((x,y))) }
        x:(@) _ "-" _ y:@ { Expression::Sub(Box::new((x,y))) }
        --
        x:(@) _ "*" _ y:@ { Expression::Mul(Box::new((x,y))) }
        x:(@) _ "/" _ y:@ { Expression::Div(Box::new((x,y))) }
        x:(@) _ "%" _ y:@ { Expression::Rem(Box::new((x,y))) }
        --
        "-" e:@ { Expression::Neg(Box::new(e)) }
        "+" e:@ { e }
        ("!"/"not") e:@ { Expression::Not(Box::new(e)) }
        --
        e:@ "["  _ i:expression() _ "]" { Expression::Index(Box::new((e,i))) }
        e:@ "." i:$identifier()  { Expression::Dot(Box::new((e,Expression::Value(Variant::str(i))))) }
        f:@ "(" _ l:(expression() ** value_separator()) _ ")" {
            Expression::FunctionCall { function: Box::new(f), arguments: l }
        }
        --
        b:block(){b}
       // --
        w:while_(){w}
        f:for_(){f}
        i:if_else(){i}
        i:if_(){i}
        f:anonymous_function(){f}
        f:function_declaration(){f}

       // --
        v:vec() { v }
        s:fstring(){s}

       // --
        "(" v:expression() ")" { v }
        d:dict() {d}
        b:true_() {b}
        b:false_() {b}
        i:$identifier() { Expression::Identifier(i.into()) }
        s:string() {s}
        n:number() {n}

    }
    pub rule expr_sequence() -> Expression
        = expr_separator()* e:(expression()**(expr_separator()+)) expr_separator()*
        {
            Expression::ExprSequence(e)
        }
});

#[cfg(test)]
mod tests {
    use super::expr_parser;
    use crate::{memory::Memory, variant::Variant};

    #[test]
    fn test_expression() {
        let ast = expr_parser::expression("1 + 2*3").unwrap();
        let result = ast.evaluate(&mut Memory::new()).unwrap();
        assert_eq!(Variant::Int(7), result);
    }

    #[test]
    fn test_string_mul() {
        let ast = expr_parser::expression(r#""a"*5"#).unwrap();
        let result = ast.evaluate(&mut Memory::new()).unwrap();
        assert_eq!(Variant::str("aaaaa"), result);
    }

    #[test]
    fn test_index() {
        let ast = expr_parser::expression("a[0]").unwrap();
        let mut memory = Memory::new();
        memory
            .set("a", Variant::vec(vec![Variant::Int(1)]))
            .unwrap();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }
    #[test]
    fn test_index_assign() {
        let ast = expr_parser::expression("a[0] = 2").unwrap();
        let mut memory = Memory::new();
        memory
            .set("a", Variant::vec(vec![Variant::Int(1)]))
            .unwrap();
        ast.evaluate(&mut memory).unwrap();
        let b = memory.get("a").unwrap();
        let a_value = b.index(&Variant::Int(0)).unwrap();
        assert_eq!(Variant::Int(2), a_value.clone());
    }
    #[test]
    fn test_double_index() {
        let ast = expr_parser::expression("a[0][0]").unwrap();
        let mut memory = Memory::new();
        memory
            .set("a", Variant::vec(vec![Variant::vec(vec![Variant::Int(1)])]))
            .unwrap();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }

    #[test]
    fn test_dict() {
        let code = r#"a = { 
            b : 1,
            "c" : 2
        }
        a.b
        "#;
        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::new();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }

    #[test]
    fn test_empty_dict() {
        let code = "a = {}";
        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::new();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::dict(&[]), a_value);
    }
    #[test]
    fn test_index_by_dot() {
        let ast = expr_parser::expression("a.b").unwrap();
        dbg!(&ast);
        let mut memory = Memory::new();
        memory
            .set("a", Variant::dict(&[(Variant::str("b"), Variant::Int(1))]))
            .unwrap();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }

    #[test]
    fn test_double_index_by_dot() {
        let ast = expr_parser::expression("a.b.c").unwrap();
        let mut memory = Memory::new();
        memory
            .set(
                "a",
                Variant::dict(&[(
                    Variant::str("b"),
                    Variant::dict(&[(Variant::str("c"), Variant::Int(1))]),
                )]),
            )
            .unwrap();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }

    #[test]
    fn test_index_assign_by_dot() {
        let ast = expr_parser::expression("a.b = 2").unwrap();
        let mut memory = Memory::new();
        memory
            .set("a", Variant::dict(&[(Variant::str("b"), Variant::Int(1))]))
            .unwrap();
        ast.evaluate(&mut memory).unwrap();
        let b = memory.get("a").unwrap();
        let a_value = b.index(&Variant::str("b")).unwrap();
        assert_eq!(Variant::Int(2), a_value.clone());
    }

    #[test]
    fn test_index_assign_declaration() {
        let ast = expr_parser::expression("a.b = 2").unwrap();
        let mut memory = Memory::new();
        memory.set("a", Variant::dict(&[])).unwrap();
        ast.evaluate(&mut memory).unwrap();
        let b = memory.get("a").unwrap();
        let a_value = b.index(&Variant::str("b")).unwrap();
        assert_eq!(Variant::Int(2), a_value.clone());
    }

    #[test]
    fn test_function_call() {
        let ast = expr_parser::expression("min(1, 2, 3)").unwrap();
        let mut memory = Memory::with_builtins();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(1), result);
    }

    #[test]
    fn test_fstring() {
        let ast = expr_parser::expression(r#"f"{1+1} = 2""#).unwrap();
        let result = ast.evaluate(&mut Memory::new()).unwrap();
        assert_eq!(Variant::str("2 = 2"), result);
    }

    #[test]
    fn test_declaration() {
        let ast = expr_parser::expression("a = 1").unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Int(1), a_value);
    }

    #[test]
    fn test_vec_ops() {
        let code = r"a = 1
        push(a,1)
        ";
        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        let r = ast.evaluate(&mut memory);
        let a_value = memory.get("a").unwrap().clone();
        assert!(r.is_err());
        assert_eq!(Variant::Int(1), a_value);
    }
    #[test]
    fn test_logical_expr_and_variables() {
        let ast = expr_parser::expr_sequence("a = 1; b = a == 1").unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("b").unwrap().clone();
        assert_eq!(Variant::Bool(true), a_value);
    }
    #[test]
    fn test_block_of_code() {
        let ast = expr_parser::expr_sequence(
            "{
            a = 1
            a = a + 1

            a
        }",
        )
        .unwrap();
        let mut memory = Memory::new();
        let result = ast.evaluate(&mut memory).unwrap();

        assert_eq!(Variant::Int(2), result);
    }
    #[test]
    fn test_while_loop() {
        let code = r"a = 0
        while a < 10 { 
            a = a + 1 
        }
        ";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Int(10), a_value);
    }
    #[test]
    fn test_for_loop() {
        let code = r"a = 0
        for i in [1,2,3,4] { 
            a = a + i 
        }
        ";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Int(10), a_value);
    }

    #[test]
    fn test_for_loop_and_if_else() {
        let code = r"a = 0
        for i in [1,2,3,4] { 
            if i % 2 == 0 {
                a = a + i
            } else {
                a = a + i*2
            }
        }";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Int(14), a_value);
    }
    #[test]
    fn test_if() {
        let code = r"a = 0
        i=2
        if i % 2 == 0 {
            a = a + i
        }";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Int(2), a_value);
    }

    #[test]
    fn function_declaration_and_usage() {
        let code = r"fun = |a,b| max(a,b)
        fun(1,2)";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(2), result);
    }
    #[test]
    fn function_declaration_and_usage_2() {
        let code = r"fun = |a,b| {
            max(a,b)
        }
        fun(1,2)";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(2), result);
    }

    #[test]
    fn function_declaration_and_usage_3() {
        let code = r"(|a,b| max(a,b))(1,2)";

        let ast = expr_parser::expr_sequence(code).unwrap();
        let mut memory = Memory::with_builtins();
        let result = ast.evaluate(&mut memory).unwrap();
        assert_eq!(Variant::Int(2), result);
    }

    #[test]
    fn test_boolean() {
        let code = r"a = true";
        let ast = expr_parser::expr_sequence(code).unwrap();
        dbg!(&ast);
        let mut memory = Memory::new();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::Bool(true), a_value);
    }

    /*  #[test]
    fn test_iterators() {
        let code = r"r  = range(0,10)
        a=r.map(|i|i*2).to_vec()
        ";
        let ast = expr_parser::expr_sequence(code).unwrap();
        dbg!(&ast);
        let mut memory = Memory::with_builtins();
        ast.evaluate(&mut memory).unwrap();
        let a_value = memory.get("a").unwrap().clone();
        assert_eq!(Variant::vec((0..10).map(|i|Variant::Int(i*2)).collect()), a_value);
    } */
}
