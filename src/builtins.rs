use crate::{memory::Memory, variant::Variant};
use bstr::ByteSlice;
use itertools::Itertools;
use std::io;
use std::rc::Rc;
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

pub fn min(args: &[Variant], _memory: &mut Memory) -> Variant {
    generate_vec_builtins("min", |v| v.iter().min().cloned().unwrap(), args)
}

pub fn max(args: &[Variant], _memory: &mut Memory) -> Variant {
    generate_vec_builtins("max", |v| v.iter().max().cloned().unwrap(), args)
}

pub fn sum(args: &[Variant], _memory: &mut Memory) -> Variant {
    let sum = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.add(&i).unwrap_or_else(Variant::error))
            .unwrap_or(Variant::Int(0))
    };
    generate_vec_builtins("sum", sum, args)
}

pub fn prod(args: &[Variant], _memory: &mut Memory) -> Variant {
    let prod = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.mul(&i).unwrap_or_else(Variant::error))
            .unwrap_or(Variant::Int(0))
    };
    generate_vec_builtins("prod", prod, args)
}

pub fn sort(args: &[Variant], _memory: &mut Memory) -> Variant {
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

pub fn sort_by(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("sort_by() must receive two arguments");
    }
    let mut v = if let Variant::Vec(v) = &args[0] {
        v.borrow_mut()
    } else {
        return Variant::error("First argument of sort_by mut be a Vec");
    };

    match &args[1] {
        Variant::NativeFunc(f) => v.sort_unstable_by_key(|i| f.call(slice::from_ref(i), memory)),
        Variant::Func(f) => v.sort_unstable_by_key(|i| {
            f.call(slice::from_ref(i), memory)
                .unwrap_or_else(Variant::error)
        }),
        f => return Variant::error(format!("Can't use {f} as a function to sort {args:?}")),
    }
    Variant::vec(v.to_vec())
}

pub fn print(args: &[Variant], _memory: &mut Memory) -> Variant {
    println!("{}", args.iter().join(" "));
    Variant::Unit
}

pub fn input(args: &[Variant], _memory: &mut Memory) -> Variant {
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

pub fn push(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() < 2 {
        return Variant::error("push function needs at least two arguments");
    }
    let Variant::Vec(v) = &args[0] else {
        return Variant::error("First argument of push function needs to be a vec");
    };
    v.borrow_mut().extend_from_slice(&args[1..]);
    Variant::Unit
}

pub fn range(args: &[Variant], _memory: &mut Memory) -> Variant {
    match args.len() {
        2 | 3 => {
            let error = Variant::error("range function arguments must be of int type");
            let Variant::Int(start) = &args[0] else {
                return error;
            };
            let Variant::Int(end) = &args[1] else {
                return error;
            };
            let Variant::Int(step) = &args.get(2).unwrap_or(&Variant::Int(1)) else {
                return error;
            };
            Variant::iterator((*start..*end).step_by((*step) as usize).map(Variant::Int))
        }

        _ => Variant::error("range function needs two or three arguments"),
    }
}

pub fn contains(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("contains function needs two arguments");
    }
    let result = match &args[0] {
        Variant::Str(s) => s.contains_str(args[1].to_string()),
        Variant::Dict(d) => d.borrow().contains_key(&args[1]),
        Variant::Vec(v) => v.borrow().contains(&args[1]),
        _ => return Variant::error("contains function with strings, dictionaries or vectors"),
    };
    Variant::Bool(result)
}

pub fn join(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("join function needs two arguments");
    }
    let Variant::Str(separator) = &args[1] else {
        return Variant::error("Second argument of join must be a string");
    };
    let separator = &separator.to_str_lossy();

    let result = match &args[0] {
        Variant::Vec(v) => v.borrow().iter().join(separator),
        Variant::Iterator(i) => i.borrow_mut().clone().to_vec(memory).iter().join(separator),
        _ => return Variant::error("Second argument of join must be a vector or an iterator"),
    };
    Variant::str(result)
}

pub fn map(args: &[Variant], _memory: &mut Memory) -> Variant {
    //dbg!("calling map");
    if args.len() != 2 {
        return Variant::error("map function needs two arguments");
    }
    args[0]
        .clone()
        .map(args[1].clone())
        .unwrap_or_else(Variant::error)
}

pub fn filter(args: &[Variant], _memory: &mut Memory) -> Variant {
    //dbg!("calling filter");
    if args.len() != 2 {
        return Variant::error("filter function needs two arguments");
    }
    args[0]
        .clone()
        .filter(args[1].clone())
        .unwrap_or_else(Variant::error)
}

pub fn to_vec(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("to_vec function needs one arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().to_variant_vec(memory),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

macro_rules! as_number {
    ($variant:expr) => {
        match $variant {
            Variant::Int(i) => *i as usize,
            Variant::Float(f) => {
                if f.fract() == 0.0 {
                    *f as usize
                } else {
                    return Variant::error("Can't slice with a fractional number");
                }
            }
            _ => return Variant::error("slice function can only be used with numbers"),
        }
    };
}

pub fn slice(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 3 {
        return Variant::error("slice function needs two arguments");
    }
    let start = as_number!(&args[1]);
    let end = as_number!(&args[2]);
    match &args[0] {
        Variant::Vec(v) => Variant::vec_slice(v.clone(), start, end),
        Variant::Str(s) => Variant::str_slice(s.clone(), start, end),
        _ => Variant::error("Only strings and vecs can be sliced"),
    }
}
