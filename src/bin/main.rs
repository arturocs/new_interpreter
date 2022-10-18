use new_interpreter::expression::Expression;
use new_interpreter::variant::Variant;

#[macro_use]
extern crate lalrpop_util;

//lalrpop_mod!(pub parser); // syntesized by LALRPOP

fn main() {
    /*     let mut memory = vec![[("_a".to_string(), Variant::int(1))].into_iter().collect()];
    dbg!(&memory);
    let ast = parser::ExpressionParser::new()
        .parse(r#"22.1 + +44 * -66 + "ee" + 20 % _a "#)
        .unwrap();
    dbg!(&ast);
    dbg!(ast.evaluate(&mut memory).unwrap());

    let ast2 = parser::ExpressionParser::new()
        .parse("{1; 2; {3}}")
        .unwrap();
    dbg!(&ast2);
    dbg!(ast2.evaluate(&mut memory).unwrap()); */
}
