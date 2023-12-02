use crate::variant::Type;
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
    memory: &mut Memory
) -> Variant {
    match args.len() {
        0 => Variant::error(format!("No arguments received on function {name}")),
        1 => {
            match &args[0] {
                Variant::Vec(v) => function(&v.borrow()),
                Variant::Iterator(i) => function(&i.borrow().clone().to_vec(memory)),
                _ => Variant::error(format!(
                    "Cannot calculate {name} of {}",
                    &args[0] 
                )),
            }
          
        }

        _ => function(args),
    }
}

pub fn min(args: &[Variant], memory: &mut Memory) -> Variant {
    generate_vec_builtins("min", |v| v.iter().min().cloned().unwrap(), args,memory)
}

pub fn max(args: &[Variant], memory: &mut Memory) -> Variant {
    generate_vec_builtins("max", |v| v.iter().max().cloned().unwrap(), args,memory)
}

pub fn sum(args: &[Variant], memory: &mut Memory) -> Variant {
    let sum = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.add(&i).unwrap_or_else(Variant::error))
            .unwrap_or(Variant::Int(0))
    };
    generate_vec_builtins("sum", sum, args,memory)
}

pub fn prod(args: &[Variant], memory: &mut Memory) -> Variant {
    let prod = |v: &[Variant]| {
        v.iter()
            .cloned()
            .reduce(|acc, i| acc.mul(&i).unwrap_or_else(Variant::error))
            .unwrap_or(Variant::Int(0))
    };
    generate_vec_builtins("prod", prod, args,memory)
}

pub fn sort(args: &[Variant], memory: &mut Memory) -> Variant {
    generate_vec_builtins(
        "sort",
        |v| {
            let mut v = v.to_owned();
            v.sort_unstable();
            Variant::vec(v)
        },
        args,
        memory
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

pub fn to_dict(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("to_dict function needs one arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().to_variant_dict(memory),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

pub fn count(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("count function needs one arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().count(memory),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

pub fn reduce(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("reduce function needs two arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().reduce(&args[1], memory).unwrap_or_else(Variant::error),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

pub fn all(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("all function needs one arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().all(memory),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

pub fn any(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("any function needs one arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().any(memory),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}


pub fn find(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("find function needs two arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().find(&args[1], memory).unwrap_or_else(Variant::error),
        Ok(e) => Variant::error(format!("{e} is not iterable")),
        Err(e) => Variant::error(e),
    }
}

pub fn for_each(args: &[Variant], memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("for_each function needs two arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => i.borrow_mut().clone().for_each(&args[1], memory),
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
        Variant::Vec(v) => Variant::vec(v.borrow()[start..end].to_vec()),
        Variant::Str(s) => Variant::str(s[start..end].as_bstr()),
        _ => Variant::error("Only strings and vecs can be sliced"),
    }
}

pub fn export_top_level_builtins() -> impl Iterator<Item = (Rc<str>, Variant)> {
    [
        ("sum", sum as fn(&[Variant], &mut Memory) -> Variant, vec![]),
        ("prod", prod, vec![]),
        ("min", min, vec![]),
        ("max", max, vec![]),
        ("sort", sort, vec![Type::Vec]),
        ("sort_by", sort_by, vec![Type::Vec]),
        ("print", print, vec![]),
        ("input", input, vec![]),
        ("push", push, vec![Type::Vec]),
        ("range", range, vec![]),
        ("contains", contains, vec![Type::Vec, Type::Dict]),
        ("join", join, vec![Type::Vec, Type::Iterator]),
        ("map", map, vec![Type::Vec, Type::Iterator]),
        ("filter", filter, vec![Type::Vec, Type::Iterator]),
        ("to_vec", to_vec, vec![Type::Vec, Type::Iterator]),
        ("to_dict", to_dict, vec![Type::Vec, Type::Iterator]),
        ("count", count, vec![Type::Vec, Type::Iterator]),
        ("reduce", reduce, vec![Type::Vec, Type::Iterator]),
        ("all", all, vec![Type::Vec, Type::Iterator]),
        ("any", any, vec![Type::Vec, Type::Iterator]),
        ("find", find, vec![Type::Vec, Type::Iterator]),
        ("for_each", for_each, vec![Type::Vec, Type::Iterator]),
        ("slice", slice, vec![Type::Vec, Type::Str]),
    ]
    .into_iter()
    .map(|(name, f, method_of)| {
        if method_of.len() > 0 {
            (name.into(), Variant::method(name, f, method_of))
        } else {
            (name.into(), Variant::native_fn(f))
        }
    })
}
