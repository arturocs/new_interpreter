#![allow(dead_code)]
#![allow(unstable_name_collisions)]
#![allow(non_snake_case)]

/* use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;
 */
use criterion::{black_box, criterion_group, criterion_main, Criterion};

use new_interpreter::expression::Expression;
use new_interpreter::memory::Memory;
use new_interpreter::variant::Variant;

fn benchmark1(c: &mut Criterion) {
    let mut variables = Memory::new();
    c.bench_function("fstring 1000 times", |b| {
        b.iter(|| {
            let a = (0..1000).fold(Expression::value(Variant::str("first")), |acc, i| {
                let expr = Expression::Fstring(vec![
                    acc,
                    Expression::Div(Box::new((
                        Expression::value(Variant::Int(i)),
                        Expression::value(Variant::Int(i + 1)),
                    ))),
                    Expression::value(Variant::str(" test B ")),
                    Expression::And(Box::new((
                        Expression::value(Variant::Bool(true)),
                        Expression::value(Variant::Bool(false)),
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
            let var = Variant::Vec(vec![
                Variant::Int(1),
                Variant::Float(2.0),
                Variant::Bool(true),
                Variant::str("hello"),
            ]);

            let a = var
                .into_iterator()
                .unwrap()
                .map(Variant::native_fn(|i| Variant::str(&i[0])))
                .unwrap()
                .filter(Variant::native_fn(|i| {
                    Variant::Bool(match &i[0] {
                        Variant::Str(s) => s.parse::<f64>().is_ok(),
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
    let mut variables = Memory::new();
    c.bench_function("integer maths", |b| {
        b.iter(|| {
            let expr = Expression::Mul(Box::new((
                Expression::Add(Box::new((
                    Expression::value(Variant::Int(1)),
                    Expression::value(Variant::Int(2)),
                ))),
                Expression::value(Variant::Int(3)),
            )));
            let val = expr.evaluate(&mut variables).unwrap();
            black_box(val)
        });
    });
}

fn benchmark4(c: &mut Criterion) {
    let mut variables = Memory::new();
    variables
        .set("v", Variant::Vec((0..100).map(Variant::Int).collect()))
        .unwrap();
    variables
        .set(
            "filter",
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
            "is_even",
            Variant::native_fn(|i| {
                Variant::Bool(i[0].rem(&Variant::Int(2)).unwrap() == Variant::Int(0))
            }),
        )
        .unwrap();
    c.bench_function("filter with native function", |b| {
        b.iter(|| {
            let expr = Expression::FunctionCall {
                function: Box::new(Expression::Identifier("filter".into())),
                arguments: vec![
                    Expression::Identifier("v".into()),
                    Expression::Identifier("is_even".into()),
                ],
            };

            black_box(expr.evaluate(&mut variables).unwrap())
        });
    });
}

fn benchmark5(c: &mut Criterion) {
    let mut variables = Memory::new();
    variables
        .set("v", Variant::Vec((0..100).map(Variant::Int).collect()))
        .unwrap();
    variables
        .set(
            "filter",
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
            "is_even",
            Variant::func(
                vec!["i".into()],
                vec![Expression::Eq(Box::new((
                    Expression::Rem(Box::new((
                        Expression::Identifier("i".to_string()),
                        Expression::value(Variant::Int(2)),
                    ))),
                    Expression::value(Variant::Int(0)),
                )))],
            ),
        )
        .unwrap();

    c.bench_function("filter with non native function", |b| {
        b.iter(|| {
            let expr = Expression::FunctionCall {
                function: Box::new(Expression::Identifier("filter".into())),
                arguments: vec![
                    Expression::Identifier("v".into()),
                    Expression::Identifier("is_even".into()),
                ],
            };

            black_box(expr.evaluate(&mut variables).unwrap())
        });
    });
}

criterion_group!(benches, benchmark1, benchmark2, benchmark3, benchmark4, benchmark5);
criterion_main!(benches);
