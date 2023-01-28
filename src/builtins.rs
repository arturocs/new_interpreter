use crate::{memory::Memory, variant::Variant};
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
                function(v)
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
            .reduce(|acc, i| acc.add(&i).unwrap_or_else(|e| Variant::error(e)))
            .unwrap()
            .clone()
    };
    generate_vec_builtins("sum", sum, args)
}

pub fn prod(args: &[Variant]) -> Variant {
    let prod = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.mul(&i).unwrap_or_else(|e| Variant::error(e)))
            .unwrap()
            .clone()
    };
    generate_vec_builtins("prod", prod, args)
}

pub fn sort(args: &[Variant]) -> Variant {
    generate_vec_builtins(
        "sort",
        |v| {
            let mut v = v.to_owned();
            v.sort_unstable();
            Variant::Vec(v)
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
                    .unwrap_or_else(|e| Variant::error(e))
            }),
            _ => {
                return Variant::error(format!(
                    "Can't use {function:?} as a function to sort {args:?}"
                ))
            }
        }

        Variant::Vec(v)
    };
    generate_vec_builtins("sort", sort_by, args)
}
