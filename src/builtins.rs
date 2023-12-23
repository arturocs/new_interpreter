use crate::iterator::{Adapter, VariantIterator};
use crate::runner;
use crate::shared::Shared;
use crate::variant::Type;
use crate::{memory::Memory, variant::Variant};
use anyhow::{anyhow, bail, Result};
use bstr::ByteSlice;
use itertools::Itertools;
use std::io;
use std::rc::Rc;
use std::slice;

macro_rules! generate_vec_builtins {
    ($name:ident, $function:expr) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
            match args.len() {
                0 => bail!(concat!(
                    "No arguments received on function ",
                    stringify!($name)
                )),
                1 => match &args[0] {
                    Variant::Vec(v) => ($function)(&v.borrow()),
                    Variant::Iterator(i) => ($function)(&i.borrow().clone().to_vec(memory)),
                    _ => bail!("Cannot calculate {} of {}", stringify!($name), &args[0]),
                },

                _ => ($function)(args),
            }
        }
    };
}

generate_vec_builtins!(min, |v: &[_]| Ok(v.iter().min().cloned().unwrap()));
generate_vec_builtins!(max, |v: &[_]| Ok(v.iter().max().cloned().unwrap()));
generate_vec_builtins!(sum, |v: &[Variant]| {
    v.iter().fold(Ok(Variant::Int(0)), |acc, i| acc?.add(&i))
});
generate_vec_builtins!(prod, |v: &[Variant]| {
    v.iter().fold(Ok(Variant::Int(1)), |acc, i| acc?.mul(&i))
});
generate_vec_builtins!(sort, |v: &[_]| {
    let mut v = v.to_owned();
    v.sort_unstable();
    Ok(Variant::vec(v))
});

pub fn sort_by(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("sort_by() must receive two arguments");
    }
    let mut v = if let Variant::Vec(v) = &args[0] {
        v.borrow_mut()
    } else {
        bail!("First argument of sort_by mut be a Vec");
    };

    let a: Result<Vec<_>> = match &args[1] {
        Variant::NativeFunc(f) => v
            .iter()
            .map(|i| f.call(slice::from_ref(i), memory))
            .collect(),
        Variant::Func(f) => v
            .iter()
            .map(|i| f.call(slice::from_ref(i), memory))
            .collect(),
        f => bail!("Can't use {f} as a function to sort {args:?}"),
    };
    let mut b = a?.into_iter().zip(v.iter()).collect_vec();
    b.sort_unstable();
    let c = b.into_iter().map(|i| i.1).cloned().collect();
    *v = c;
    Ok(args[0].clone())
}

pub fn print(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    println!("{}", args.iter().join(" "));
    Ok(Variant::Unit)
}

pub fn input(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if !args.is_empty() {
        bail!("input function cannot receive arguments");
    }
    let mut buffer = String::new();
    let result = io::stdin().read_line(&mut buffer);
    if let Err(e) = result {
        Err(e.into())
    } else {
        Ok(Variant::str(buffer))
    }
}

pub fn push(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() < 2 {
        bail!("push() method needs at least two arguments");
    }
    let Variant::Vec(v) = &args[0] else {
        bail!("First argument of push method needs to be a vec");
    };
    v.borrow_mut().extend_from_slice(&args[1..]);
    Ok(Variant::Unit)
}

pub fn range(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    let error = Err(anyhow!("range function arguments must be of int type"));
    match args.len() {
        1 => {
            let Variant::Int(end) = &args[0] else {
                return error;
            };
            Ok(Variant::iterator((0..*end).map(Variant::Int)))
        }
        2 | 3 => {
            let Variant::Int(start) = &args[0] else {
                return error;
            };
            let Variant::Int(end) = &args[1] else {
                return error;
            };
            let Variant::Int(step) = &args.get(2).unwrap_or(&Variant::Int(1)) else {
                return error;
            };
            Ok(Variant::iterator(
                (*start..*end).step_by((*step) as usize).map(Variant::Int),
            ))
        }

        _ => bail!("range function needs two or three arguments"),
    }
}

pub fn contains(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("contains function needs two arguments");
    }
    let result = match &args[0] {
        Variant::Str(s) => s.contains_str(args[1].to_string()),
        Variant::Dict(d) => d.borrow().contains_key(&args[1]),
        Variant::Vec(v) => v.borrow().contains(&args[1]),
        _ => bail!("contains function with strings, dictionaries or vectors"),
    };
    Ok(Variant::Bool(result))
}

pub fn join(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("join() method needs two arguments");
    }
    let Variant::Str(separator) = &args[1] else {
        bail!("Second argument of join must be a string");
    };
    let separator = &separator.to_str_lossy();

    let result = match &args[0] {
        Variant::Vec(v) => v.borrow().iter().join(separator),
        Variant::Iterator(i) => i.borrow_mut().clone().to_vec(memory).iter().join(separator),
        _ => bail!("First argument of join must be a vector or an iterator"),
    };
    Ok(Variant::str(result))
}

macro_rules! generate_iterator_adapters_builtins {
    ($name:ident, $method:expr) => {
        pub fn $name(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
            if args.len() != 2 {
                bail!(concat!(stringify!($name), "() function needs two arguments"));
            }
            let Ok(Variant::Iterator(i)) = args[0].clone().into_iterator() else {
                bail!(format!("{} is not iterable", args[0]));
            };

            $method(&mut i.borrow_mut(), args[1].clone());
            Ok(Variant::Iterator(i))
        }
    };
}

macro_rules! generate_iterator_adapters_builtins_without_args {
    ($name:ident, $method:expr) => {
        pub fn $name(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
            if args.len() != 1 {
                bail!(concat!(stringify!($name), "() function needs two arguments"));
            }
            match args[0].clone().into_iterator() {
                Ok(Variant::Iterator(i)) => {
                    $method(&mut i.borrow_mut());
                    Ok(Variant::Iterator(i))
                }
                Ok(e) => bail!("{e} is not iterable"),
                e => e,
            }
        }
    };
}

generate_iterator_adapters_builtins!(map, VariantIterator::map);
generate_iterator_adapters_builtins!(filter, VariantIterator::filter);
generate_iterator_adapters_builtins!(zip, VariantIterator::zip);
generate_iterator_adapters_builtins!(take, VariantIterator::take);
generate_iterator_adapters_builtins!(skip, VariantIterator::skip);
generate_iterator_adapters_builtins!(step_by, VariantIterator::step_by);
generate_iterator_adapters_builtins!(flat_map, VariantIterator::flat_map);
generate_iterator_adapters_builtins_without_args!(flatten, VariantIterator::flatten);
generate_iterator_adapters_builtins_without_args!(enumerate, VariantIterator::enumerate);

macro_rules! generate_iterator_evaluator_builtins {
    ($name:ident,$method:ident) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
            if args.len() != 1 {
                bail!(concat!(stringify!($name), " function needs one argument"));
            }
            match args[0].clone().into_iterator() {
                Ok(Variant::Iterator(i)) => Ok(i.borrow_mut().clone().$method(memory)),
                Ok(e) => bail!("{e} is not iterable"),
                e => e,
            }
        }
    };
}

macro_rules! generate_iterator_evaluator_with_arguments_builtins {
    ($name:ident,$method:ident) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
            if args.len() != 2 {
                bail!(concat!(stringify!($name), " function needs two arguments"));
            }
            match args[0].clone().into_iterator() {
                Ok(Variant::Iterator(i)) => i.borrow_mut().clone().$method(&args[1], memory),
                Ok(e) => bail!("{e} is not iterable"),
                e => e,
            }
        }
    };
}

generate_iterator_evaluator_builtins!(to_vec, to_variant_vec);
generate_iterator_evaluator_builtins!(to_dict, to_variant_dict);
generate_iterator_evaluator_builtins!(count, count);
generate_iterator_evaluator_builtins!(all, all);
generate_iterator_evaluator_builtins!(any, any);
generate_iterator_evaluator_with_arguments_builtins!(reduce, reduce);
generate_iterator_evaluator_with_arguments_builtins!(find, find);

pub fn for_each(args: &[Variant], memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("for_each function needs two arguments");
    }
    match args[0].clone().into_iterator() {
        Ok(Variant::Iterator(i)) => Ok(i.borrow_mut().clone().for_each(&args[1], memory)),
        Ok(e) => bail!("{e} is not iterable"),
        e => e,
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
                    bail!("Can't slice with a fractional number");
                }
            }
            _ => bail!("slice function can only be used with numbers"),
        }
    };
}

pub fn slice(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 3 {
        bail!("slice function needs two arguments");
    }
    let start = as_number!(&args[1]);
    let end = as_number!(&args[2]);
    match &args[0] {
        Variant::Vec(v) => Ok(Variant::vec(v.borrow()[start..end].to_vec())),
        Variant::Str(s) => Ok(Variant::str(s[start..end].as_bstr())),
        _ => bail!("Only strings and vecs can be sliced"),
    }
}

pub fn read_file(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("read_file function needs one argument");
    }
    let Variant::Str(path) = &args[0] else {
        bail!("read_file function needs a string as argument");
    };
    let path = path.to_str_lossy();

    let content = std::fs::read(path.as_ref())?;
    Ok(Variant::Str(Rc::new(content.into())))
}

pub fn write_to_file(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("write_to_file function needs two arguments");
    }
    let Variant::Str(path) = &args[0] else {
        bail!("write_to_file function needs a string as first argument");
    };
    let path = path.to_str_lossy();
    let content = args[1].to_string();
    std::fs::write(path.as_ref(), content)?;
    Ok(Variant::Unit)
}

pub fn items(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("items function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Ok(Variant::vec(
            d.borrow()
                .iter()
                .map(|(k, v)| Variant::vec(vec![k.clone(), v.clone()]))
                .collect(),
        )),
        _ => bail!("items function needs a dict as argument"),
    }
}

pub fn keys(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("keys function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Ok(Variant::vec(d.borrow().keys().cloned().collect())),
        _ => bail!("keys function needs a dict as argument"),
    }
}

pub fn values(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("values() function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Ok(Variant::vec(d.borrow().values().cloned().collect())),
        _ => bail!("values() function needs a dict as argument"),
    }
}

pub fn int(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("int() function needs one argument");
    }

    let result = match &args[0] {
        &Variant::Bool(b) => Variant::Int(b as i64),
        &Variant::Int(i) => Variant::Int(i),
        &Variant::Float(f) => Variant::Int(f as i64),
        Variant::Str(s) => s.to_str_lossy().parse().map(Variant::Int)?,
        e => bail!("{e} cannot be parsed as integer"),
    };
    Ok(result)
}

pub fn float(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("float() function needs one argument");
    }

    let result = match &args[0] {
        &Variant::Bool(b) => Variant::Float(b as u8 as f64),
        &Variant::Int(i) => Variant::Float(i as f64),
        &Variant::Float(f) => Variant::Float(f),
        Variant::Str(s) => s.to_str_lossy().parse().map(Variant::Float)?,
        e => bail!("{e} cannot be parsed as integer"),
    };
    Ok(result)
}

pub fn split(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("split() method needs two arguments");
    }
    match (&args[0], &args[1]) {
        (Variant::Str(s1), Variant::Str(s2)) => Ok(Variant::vec(
            s1.to_str_lossy()
                .split(s2.to_str_lossy().as_ref())
                .map(Variant::str)
                .collect(),
        )),
        _ => bail!("split() method only works on strings"),
    }
}

pub fn generator(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("generator() method needs one argument");
    }

    match &args[0] {
        Variant::Func(f) => Ok(Variant::Iterator(Shared::new(
            VariantIterator::from_adapter(
                Adapter::Generator(Variant::Func(f.clone())),
                std::iter::empty(),
            ),
        ))),
        _ => bail!("generator() method only works on functions"),
    }
}

pub fn err(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    match args.len() {
        0 => Ok(Variant::error("Emtpy error message")),
        1 => match &args[0] {
            Variant::Str(s) => Ok(Variant::error(s)),
            _ => bail!("err() method only works on strings"),
        },
        _ => bail!("err() method needs zero or one arguments"),
    }
}

pub fn type_(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("type() method needs one argument");
    }
    Ok(Variant::str(args[0].get_type().to_string()))
}

pub fn assert_eq(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 2 {
        bail!("assert_eq() method needs two arguments");
    }
    match args.iter().find(|i| i.is_error()) {
        Some(e) => Ok(e.clone()),
        None => {
            if args[0] == args[1] {
                Ok(Variant::Unit)
            } else {
                bail!("assert_eq() failed: {} != {}", args[0], args[1])
            }
        }
    }
}

pub fn assert_(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("assert() function needs one argument");
    }

    if args[0].is_true().unwrap_or(false) {
        Ok(Variant::Unit)
    } else {
        Ok(Variant::error("Assertion failed"))
    }
}

pub fn import(args: &[Variant], _memory: &mut Memory) -> Result<Variant> {
    if args.len() != 1 {
        bail!("import() function needs one argument");
    }
    let Variant::Str(path) = &args[0] else {
        bail!("import() function needs a string as argument");
    };
    let path = path.to_str_lossy();
    let (_, memory) = runner::run_file(path.as_ref())?;
    Ok(Variant::Dict(Shared::new(memory.to_dict())))
}

pub fn export_global_metods() -> impl Iterator<Item = (Rc<str>, Variant)> {
    let sum = sum as fn(&[Variant], &mut Memory) -> Result<Variant>;
    [
        ("sum", sum, vec![Type::Vec, Type::Iterator]),
        ("prod", prod, vec![Type::Vec, Type::Iterator]),
        ("min", min, vec![Type::Vec, Type::Iterator]),
        ("max", max, vec![Type::Vec, Type::Iterator]),
        ("sort", sort, vec![Type::Vec]),
        ("sort_by", sort_by, vec![Type::Vec]),
        ("push", push, vec![Type::Vec]),
        ("contains", contains, vec![Type::Vec]),
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
        ("split", split, vec![Type::Str]),
        ("step_by", step_by, vec![Type::Vec, Type::Iterator]),
        ("zip", zip, vec![Type::Vec, Type::Iterator]),
        ("take", take, vec![Type::Vec, Type::Iterator]),
        ("skip", skip, vec![Type::Vec, Type::Iterator]),
        ("flat_map", flat_map, vec![Type::Vec, Type::Iterator]),
        ("enumerate",enumerate,vec![Type::Vec,Type::Iterator]),
        ("flatten",flatten,vec![Type::Vec,Type::Iterator])
    ]
    .into_iter()
    .map(|(name, f, method_of)| (name.into(), Variant::method(name, f, method_of)))
}

pub fn export_top_level_builtins() -> impl Iterator<Item = (Rc<str>, Variant)> {
    [
        ("min", min as fn(&[Variant], &mut Memory) -> Result<Variant>),
        ("max", max),
        ("int", int),
        ("float", float),
        ("print", print),
        ("input", input),
        ("range", range),
        ("read_file", read_file),
        ("write_to_file", write_to_file),
        ("items", items),
        ("keys", keys),
        ("values", values),
        ("assert", assert_),
        ("assert_eq", assert_eq),
        ("generator", generator),
        ("err", err),
        ("type", type_),
        ("import", import),
    ]
    .into_iter()
    .map(|(name, f)| (name.into(), Variant::native_fn(Some(name), f)))
}
