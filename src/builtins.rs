use crate::iterator::{Adapter, VariantIterator};
use crate::shared::Shared;
use crate::variant::Type;
use crate::{memory::Memory, variant::Variant};
use bstr::ByteSlice;
use itertools::Itertools;
use std::io;
use std::rc::Rc;
use std::slice;

macro_rules! generate_vec_builtins {
    ($name:ident, $function:expr) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Variant {
            match args.len() {
                0 => Variant::error(concat!(
                    "No arguments received on function ",
                    stringify!($name)
                )),
                1 => match &args[0] {
                    Variant::Vec(v) => ($function)(&v.borrow()),
                    Variant::Iterator(i) => ($function)(&i.borrow().clone().to_vec(memory)),
                    _ => Variant::error(format!(
                        "Cannot calculate {} of {}",
                        stringify!($name),
                        &args[0]
                    )),
                },

                _ => ($function)(args),
            }
        }
    };
}

generate_vec_builtins!(min, |v: &[_]| v.iter().min().cloned().unwrap());
generate_vec_builtins!(max, |v: &[_]| v.iter().max().cloned().unwrap());
generate_vec_builtins!(sum, |v: &[Variant]| {
    v.iter()
        .cloned()
        .reduce(|acc, i| acc.add(&i).unwrap_or_else(Variant::error))
        .unwrap_or(Variant::Int(0))
});
generate_vec_builtins!(prod, |v: &[Variant]| {
    v.iter()
        .cloned()
        .reduce(|acc, i| acc.mul(&i).unwrap_or_else(Variant::error))
        .unwrap_or(Variant::Int(0))
});
generate_vec_builtins!(sort, |v: &[_]| {
    let mut v = v.to_owned();
    v.sort_unstable();
    Variant::vec(v)
});

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
    let error = Variant::error("range function arguments must be of int type");
    match args.len() {
        1 => {
            let Variant::Int(end) = &args[0] else {
                return error;
            };
            Variant::iterator((0..*end).map(Variant::Int))
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

macro_rules! generate_iterator_adapters_builtins {
    ($name:ident, $method:expr) => {
        pub fn $name(args: &[Variant], _memory: &mut Memory) -> Variant {
            if args.len() != 2 {
                return Variant::error(concat!(stringify!($name), " function needs two arguments"));
            }
            let Ok(Variant::Iterator(i)) = args[0].clone().into_iterator() else {
                return Variant::error(format!("{} is not iterable", args[0]));
            };

            $method(&mut i.borrow_mut(), args[1].clone());
            Variant::Iterator(i)
        }
    };
}

generate_iterator_adapters_builtins!(map, VariantIterator::map);
generate_iterator_adapters_builtins!(filter, VariantIterator::filter);
generate_iterator_adapters_builtins!(zip, VariantIterator::zip);
generate_iterator_adapters_builtins!(take, VariantIterator::take);
generate_iterator_adapters_builtins!(skip, VariantIterator::skip);
generate_iterator_adapters_builtins!(step_by, VariantIterator::step_by);

macro_rules! generate_iterator_evaluator_builtins {
    ($name:ident,$method:ident) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Variant {
            if args.len() != 1 {
                return Variant::error(concat!(stringify!($name), " function needs one argument"));
            }
            match args[0].clone().into_iterator() {
                Ok(Variant::Iterator(i)) => i.borrow_mut().clone().$method(memory),
                Ok(e) => Variant::error(format!("{e} is not iterable")),
                Err(e) => Variant::error(e),
            }
        }
    };
}

macro_rules! generate_iterator_evaluator_with_arguments_builtins {
    ($name:ident,$method:ident) => {
        pub fn $name(args: &[Variant], memory: &mut Memory) -> Variant {
            if args.len() != 2 {
                return Variant::error(concat!(stringify!($name), " function needs two arguments"));
            }
            match args[0].clone().into_iterator() {
                Ok(Variant::Iterator(i)) => i
                    .borrow_mut()
                    .clone()
                    .$method(&args[1], memory)
                    .unwrap_or_else(Variant::error),
                Ok(e) => Variant::error(format!("{e} is not iterable")),
                Err(e) => Variant::error(e),
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

pub fn read_file(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("read_file function needs one argument");
    }
    let Variant::Str(path) = &args[0] else {
        return Variant::error("read_file function needs a string as argument");
    };
    let path = path.to_str_lossy();
    let content = std::fs::read(path.as_ref());
    match content {
        Ok(content) => Variant::Str(Rc::new(content.into())),
        Err(e) => Variant::error(e),
    }
}

pub fn write_to_file(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("write_to_file function needs two arguments");
    }
    let Variant::Str(path) = &args[0] else {
        return Variant::error("write_to_file function needs a string as first argument");
    };
    let path = path.to_str_lossy();
    let content = args[1].to_string();
    let result = std::fs::write(path.as_ref(), content);
    match result {
        Ok(_) => Variant::Unit,
        Err(e) => Variant::error(e),
    }
}

pub fn items(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("items function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Variant::vec(
            d.borrow()
                .iter()
                .map(|(k, v)| Variant::vec(vec![k.clone(), v.clone()]))
                .collect(),
        ),
        _ => Variant::error("items function needs a dict as argument"),
    }
}

pub fn keys(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("keys function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Variant::vec(d.borrow().keys().cloned().collect()),
        _ => Variant::error("keys function needs a dict as argument"),
    }
}

pub fn values(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("values() function needs one argument");
    }
    match &args[0] {
        Variant::Dict(d) => Variant::vec(d.borrow().values().cloned().collect()),
        _ => Variant::error("values() function needs a dict as argument"),
    }
}

pub fn int(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("int() function needs one argument");
    }

    match &args[0] {
        &Variant::Bool(b) => Variant::Int(b as i64),
        &Variant::Int(i) => Variant::Int(i),
        &Variant::Float(f) => Variant::Int(f as i64),
        Variant::Str(s) => s
            .to_str_lossy()
            .parse()
            .map(Variant::Int)
            .unwrap_or_else(Variant::error),
        e => Variant::error(format!("{e} cannot be parsed as integer")),
    }
}

pub fn float(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("float() function needs one argument");
    }

    match &args[0] {
        &Variant::Bool(b) => Variant::Float(b as u8 as f64),
        &Variant::Int(i) => Variant::Float(i as f64),
        &Variant::Float(f) => Variant::Float(f),
        Variant::Str(s) => s
            .to_str_lossy()
            .parse()
            .map(Variant::Float)
            .unwrap_or_else(Variant::error),
        e => Variant::error(format!("{e} cannot be parsed as integer")),
    }
}

pub fn assert_(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("assert() function needs one argument");
    }

    if args[0].is_true().unwrap_or(false) {
        Variant::Unit
    } else {
        Variant::error("Assertion failed")
    }
}

pub fn split(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 2 {
        return Variant::error("split() method needs two arguments");
    }
    match (&args[0], &args[1]) {
        (Variant::Str(s1), Variant::Str(s2)) => Variant::vec(
            s1.to_str_lossy()
                .split(s2.to_str_lossy().as_ref())
                .map(Variant::str)
                .collect(),
        ),
        _ => Variant::error("split() method only works on strings"),
    }
}

pub fn generator(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("generator() method needs one argument");
    }

    match &args[0] {
        Variant::Func(f) => Variant::Iterator(Shared::new(VariantIterator::from_adapter(
            Adapter::Generator(Variant::Func(f.clone())),
            std::iter::empty(),
        ))),
        _ => Variant::error("generator() method only works on functions"),
    }
}

pub fn err(args: &[Variant], _memory: &mut Memory) -> Variant {
    match args.len() {
        0 => Variant::error("Emtpy error"),
        1 => match &args[0] {
            Variant::Str(s) => Variant::error(s),
            _ => Variant::error("err() method only works on strings"),
        },
        _ => Variant::error("err() method needs zero or one arguments"),
    }
}

pub fn type_(args: &[Variant], _memory: &mut Memory) -> Variant {
    if args.len() != 1 {
        return Variant::error("typeof() method needs one argument");
    }
    Variant::str(args[0].get_type().to_string())
}

pub fn export_global_metods() -> impl Iterator<Item = (Rc<str>, Variant)> {
    let sum = sum as fn(&[Variant], &mut Memory) -> Variant;
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
    ]
    .into_iter()
    .map(|(name, f, method_of)| (name.into(), Variant::method(name, f, method_of)))
}

pub fn export_top_level_builtins() -> impl Iterator<Item = (Rc<str>, Variant)> {
    [
        ("min", min as fn(&[Variant], &mut Memory) -> Variant),
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
        ("generator", generator),
        ("err", err),
        ("type", type_),
    ]
    .into_iter()
    .map(|(name, f)| (name.into(), Variant::native_fn(Some(name), f)))
}
