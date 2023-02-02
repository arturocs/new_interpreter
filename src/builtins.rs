use crate::{memory::Memory, variant::Variant};
use itertools::Itertools;
use std::io;
use std::slice;
fn generate_vec_builtins(
    name: &str,
    function: impl FnOnce(&[Variant]) -> Variant,
    args: &[Variant],
) -> Variant {
    match args.len() {
        0 => Variant::error(format!("No arguments received on function {name}")),
        1 => {
            if let Variant::Vec(v) = &args[0] {
                function(&v.borrow())
            } else {
                Variant::error(format!("Cannot calculate {name} of {}", &args[0]))
            }
        }

        _ => function(args),
    }
}

pub fn min(args: &[Variant]) -> Variant {
    generate_vec_builtins("min", |v| v.iter().min().cloned().unwrap(), args)
}

pub fn max(args: &[Variant]) -> Variant {
    generate_vec_builtins("max", |v| v.iter().max().cloned().unwrap(), args)
}

pub fn sum(args: &[Variant]) -> Variant {
    let sum = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.add(&i).unwrap_or_else(Variant::error))
            .unwrap()
    };
    generate_vec_builtins("sum", sum, args)
}

pub fn prod(args: &[Variant]) -> Variant {
    let prod = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.mul(&i).unwrap_or_else(Variant::error))
            .unwrap()
    };
    generate_vec_builtins("prod", prod, args)
}

pub fn sort(args: &[Variant]) -> Variant {
    generate_vec_builtins(
        "sort",
        |v| {
            let mut v = v.to_owned();
            v.sort_unstable();
            Variant::vec(v)
        },
        args,
    )
}

pub fn sort_by(args: &[Variant], function: Variant, memory: &mut Memory) -> Variant {
    let sort_by = |v: &[Variant]| {
        let mut v = v.to_owned();
        match function {
            Variant::NativeFunc(f) => v.sort_unstable_by_key(|i| f.call(slice::from_ref(i))),
            Variant::Func(f) => v.sort_unstable_by_key(|i| {
                f.call(slice::from_ref(i), memory)
                    .unwrap_or_else(Variant::error)
            }),
            _ => {
                return Variant::error(format!(
                    "Can't use {function:?} as a function to sort {args:?}"
                ))
            }
        }

        Variant::vec(v)
    };
    generate_vec_builtins("sort", sort_by, args)
}

pub fn print(args: &[Variant]) -> Variant {
    let s: String = args
        .iter()
        .map(|i| i.to_string())
        .intersperse(" ".into())
        .collect();
    println!("{s}");
    Variant::error("print function does not return a value")
}

pub fn input(args: &[Variant]) -> Variant {
    if !args.is_empty() {
        return Variant::error("input function cannot receive arguments");
    }
    let mut buffer = String::new();
    let result = io::stdin().read_line(&mut buffer);
    if let Err(e) = result {
        Variant::error(e)
    } else {
        Variant::str(buffer)
    }
}

pub fn push(args: &[Variant]) -> Variant {
    if args.len() < 2 {
        return Variant::error("push function needs at least two arguments");
    }
    let Variant::Vec(v) = &args[0] else {
        return Variant::error("First argument of push function needs to be a vec")
    };
    let mut v2 = v.borrow_mut();
    for i in &args[1..] {
        v2.push(i.clone());
    }
    args[0].clone()
}
