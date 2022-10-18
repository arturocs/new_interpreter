#![allow(dead_code)]
#![allow(unstable_name_collisions)]
#![allow(non_snake_case)]
use ahash::AHashMap;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

use new_interpreter::expression::Expression;
use new_interpreter::variant::{Variant, VariantEnum};

fn benchmark1(c: &mut Criterion) {
    let mut variables = vec![AHashMap::default()];
    c.bench_function("fstring 1000 times", |b| {
        b.iter(|| {
            let a = (0..1000).fold(Expression::value(Variant::str("first")), |acc, i| {
                let expr = Expression::Fstring(vec![
                    acc,
                    Expression::Div(Box::new((
                        Expression::value(Variant::int(i)),
                        Expression::value(Variant::int(i + 1)),
                    ))),
                    Expression::value(Variant::str(" test B ")),
                    Expression::And(Box::new((
                        Expression::value(Variant::bool(true)),
                        Expression::value(Variant::bool(false)),
                    ))),
                    Expression::value(Variant::str(" test C")),
                ]);
                let val = expr.evaluate(&mut variables).unwrap();
                Expression::value(val)
            });
            black_box(a)
        });
    });
}
fn benchmark2(c: &mut Criterion) {
    c.bench_function("filter map reduce", |b| {
        b.iter(|| {
            let var = Variant::vec(vec![
                Variant::int(1),
                Variant::float(2.0),
                Variant::bool(true),
                Variant::str("hello"),
            ]);

            let a = var
                .into_iterator()
                .unwrap()
                .map(Variant::native_fn(|i| Variant::str(i[0].clone())))
                .unwrap()
                .filter(Variant::native_fn(|i| {
                    Variant::bool(match &*i[0].0.borrow() {
                        VariantEnum::Str(s) => s.parse::<f64>().is_ok(),
                        _ => false,
                    })
                }))
                .unwrap()
                .reduce(Variant::native_fn(|i| i[0].add(&i[1]).unwrap()))
                .unwrap();
            black_box(a)
        });
    });
}

fn benchmark3(c: &mut Criterion) {
    let mut variables = vec![AHashMap::default()];
    c.bench_function("integer maths", |b| {
        b.iter(|| {
            let expr = Expression::Mul(Box::new((
                Expression::Add(Box::new((
                    Expression::value(Variant::int(1)),
                    Expression::value(Variant::int(2)),
                ))),
                Expression::value(Variant::int(3)),
            )));
            let val = expr.evaluate(&mut variables).unwrap();
            black_box(val)
        });
    });
}

fn benchmark4(c: &mut Criterion) {
    let mut variables = vec![AHashMap::default()];
    variables[0].insert(
        "v".to_string(),
        Variant::vec((0..100).map(Variant::int).collect()),
    );
    variables[0].insert(
        "filter".to_string(),
        Variant::native_fn(|i| {
            let iter = &i[0];
            let func = &i[1];
            iter.clone()
                .filter(func.clone())
                .unwrap()
                .into_vec()
                .unwrap()
        }),
    );

    variables[0].insert(
        "is_even".to_string(),
        Variant::native_fn(|i| {
            Variant::bool(i[0].rem(&Variant::int(2)).unwrap() == Variant::int(0))
        }),
    );
    c.bench_function("filter with native function", |b| {
        b.iter(|| {
            let expr = Expression::FunctionCall {
                function: Box::new(Expression::Identifier("filter".to_string())),
                arguments: vec![
                    Expression::Identifier("v".to_string()),
                    Expression::Identifier("is_even".to_string()),
                ],
            };

            black_box(expr.evaluate(&mut variables).unwrap())
        });
    });
}

fn benchmark5(c: &mut Criterion) {
    let mut variables = vec![AHashMap::default()];
    variables[0].insert(
        "v".to_string(),
        Variant::vec((0..100).map(Variant::int).collect()),
    );
    variables[0].insert(
        "filter".to_string(),
        Variant::native_fn(|i| {
            let iter = &i[0];
            let func = &i[1];
            iter.clone()
                .filter(func.clone())
                .unwrap()
                .into_vec()
                .unwrap()
        }),
    );

    variables[0].insert(
        "is_even".to_string(),
        Variant::func(
            vec!["i".to_string()],
            vec![Expression::Eq(Box::new((
                Expression::Rem(Box::new((
                    Expression::Identifier("i".to_string()),
                    Expression::value(Variant::int(2)),
                ))),
                Expression::value(Variant::int(0)),
            )))],
        ),
    );

    c.bench_function("filter with non native function", |b| {
        b.iter(|| {
            let expr = Expression::FunctionCall {
                function: Box::new(Expression::Identifier("filter".to_string())),
                arguments: vec![
                    Expression::Identifier("v".to_string()),
                    Expression::Identifier("is_even".to_string()),
                ],
            };

            black_box(expr.evaluate(&mut variables).unwrap())
        });
    });
}

criterion_group!(benches, benchmark1, benchmark2, benchmark3, benchmark4, benchmark5);
criterion_main!(benches);
