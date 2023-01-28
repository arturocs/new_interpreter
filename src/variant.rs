#![allow(dead_code)]
#![allow(unstable_name_collisions)]
#![allow(non_snake_case)]

use crate::{
    expression::Expression,
    function::{Function, NativeFunction},
    memory::Memory,
};
use ahash::RandomState;
use anyhow::{anyhow, Result};
use dyn_clone::DynClone;
use indexmap::IndexMap;
use itertools::Itertools;
use regex::Regex;
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
};
use unicode_segmentation::UnicodeSegmentation;

pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug + DynClone {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug + DynClone {}

pub(crate) type Int = i64;
pub(crate) type Float = f64;
type Dictionary = IndexMap<Variant, Variant, RandomState>;
dyn_clone::clone_trait_object!(VariantIter);
#[derive(Debug, Clone)]
pub enum Variant {
    Error(String),
    Int(Int),
    Float(Float),
    Bool(bool),
    Byte(u8),
    Vec(Vec<Variant>),
    Str(String),
    Dict(Box<Dictionary>),
    Regex(Regex),
    Iterator(Box<dyn VariantIter>),
    NativeFunc(NativeFunction),
    Func(Box<Function>),
}

impl Default for Variant {
    fn default() -> Self {
        Variant::Error("Uninitialized value".to_string())
    }
}

impl Ord for Variant {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Variant::Error(a), Variant::Error(b)) => a.cmp(b),
            (&Variant::Int(a), Variant::Float(b)) => (a as Float).total_cmp(b),
            (&Variant::Float(a), &Variant::Int(b)) => a.total_cmp(&(b as Float)),
            (&Variant::Int(a), Variant::Int(b)) => a.cmp(b),
            (&Variant::Float(a), Variant::Float(b)) => a.total_cmp(b),
            (&Variant::Bool(a), Variant::Bool(b)) => a.cmp(b),
            (&Variant::Byte(a), Variant::Byte(b)) => a.cmp(b),
            // (Variant::Bytes(a), Variant::Bytes(b)) => a.cmp(b),
            (Variant::Str(a), Variant::Str(b)) => a.cmp(b),
            (Variant::Dict(a), Variant::Dict(b)) => a.iter().cmp(b.iter()),
            (Variant::Vec(a), Variant::Vec(b)) => a.cmp(b),
            (Variant::Regex(a), Variant::Regex(b)) => a.as_str().cmp(b.as_str()),
            (Variant::Iterator(a), Variant::Iterator(b)) => a.clone().cmp(b.clone()),
            (Variant::NativeFunc(a), Variant::NativeFunc(b)) => {
                (a as *const _ as usize).cmp(&(b as *const _ as usize))
            }
            (Variant::Func(a), Variant::Func(b)) => a.cmp(b),
            (a, b) => a.get_tag().cmp(&b.get_tag()),
        }
    }
}

impl PartialOrd for Variant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Variant {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&Variant::Int(a), &Variant::Float(b)) => (a as Float) == b,
            (&Variant::Float(a), &Variant::Int(b)) => a == (b as Float),
            (&Variant::Int(a), &Variant::Int(b)) => a == b,
            (&Variant::Float(a), &Variant::Float(b)) => a == b,
            (&Variant::Bool(a), &Variant::Bool(b)) => a == b,
            (Variant::Error(a), Variant::Error(b)) => a == b,
            (&Variant::Byte(a), &Variant::Byte(b)) => a == b,
            (Variant::Str(a), Variant::Str(b)) => a == b,
            (Variant::Dict(a), Variant::Dict(b)) => a == b,
            (Variant::Vec(a), Variant::Vec(b)) => a == b,
            (Variant::Regex(a), Variant::Regex(b)) => a.as_str() == b.as_str(),
            (Variant::Iterator(a), Variant::Iterator(b)) => a.clone().eq(b.clone()),
            (Variant::NativeFunc(a), Variant::NativeFunc(b)) => {
                (a as *const _ as usize).eq(&(b as *const _ as usize))
            }
            (Variant::Func(a), Variant::Func(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Variant {}

impl fmt::Display for Variant {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Variant::Bool(b) => write!(fmt, "{b}"),
            Variant::Float(f) => write!(fmt, "{f}"),
            Variant::Int(i) => write!(fmt, "{i}"),
            Variant::Str(s) => write!(fmt, "{s}"),
            Variant::Error(e) => write!(fmt, "Error: {e}"),
            Variant::Vec(v) => {
                let content: String = v
                    .iter()
                    .map(Variant::to_string_in_collection)
                    .intersperse(", ".to_string())
                    .collect();
                write!(fmt, "[{content}]")
            }
            Variant::Dict(d) => {
                let content: String = d
                    .iter()
                    .map(|(v1, v2)| {
                        let s1 = v1.to_string_in_collection();
                        let s2 = v2.to_string_in_collection();
                        format!("{s1} : {s2}")
                    })
                    .intersperse(", ".to_string())
                    .collect();
                write!(fmt, "{{{content}}}")
            }
            Variant::Func(a) => write!(fmt, "Function at {:#X}", a as *const _ as usize),
            /* Variant::Bytes(v) => {
                let s: String = v.iter().map(|b| format!("\\{:#01x}", b)).collect();
                write!(fmt, "{s}")
            } */
            Variant::Byte(b) => write!(fmt, "\\{:#01x}", b),
            Variant::Regex(r) => write!(fmt, "{}", r.as_str()),
            Variant::Iterator(i) => write!(fmt, "{i:?}"),
            Variant::NativeFunc(f) => {
                write!(fmt, "Native function at {:?}", f as *const _)
            }
        }
    }
}

impl Hash for Variant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Variant::Error(e) => {
                0_u8.hash(state);
                e.hash(state)
            }
            Variant::Int(a) => a.hash(state),
            Variant::Float(a) => a.to_bits().hash(state),
            Variant::Bool(a) => a.hash(state),
            Variant::Str(a) => a.hash(state),
            Variant::Vec(a) => a.hash(state),
            Variant::Dict(a) => a.iter().for_each(|i| i.hash(state)),
            Variant::Func(f) => f.hash(state),
            //Variant::Bytes(v) => v.hash(state),
            Variant::Byte(b) => b.hash(state),
            Variant::Regex(r) => r.as_str().hash(state),
            Variant::Iterator(a) => a.clone().for_each(|i| i.hash(state)),
            Variant::NativeFunc(f) => (&f as *const _ as usize).hash(state),
        };
    }
}

fn apply_op_between_vecs(
    v1: &[Variant],
    v2: &[Variant],
    op: fn(&Variant, &Variant) -> Result<Variant>,
) -> Result<Variant> {
    let (bigger, smaller) = if v1.len() > v2.len() {
        (v1, v2)
    } else {
        (v2, v1)
    };
    let mut result = bigger.to_owned();
    for (i, v) in smaller.iter().enumerate() {
        unsafe { *result.get_unchecked_mut(i) = op(result.get_unchecked(i), v)? }
    }
    Ok(Variant::Vec(result))
}

impl Variant {
    fn get_tag(&self) -> u8 {
        unsafe { *(self as *const _ as *const u8) }
    }

    pub fn str(s: impl ToString) -> Variant {
        Variant::Str(s.to_string())
    }

    pub fn error(e: impl ToString) -> Variant {
        Variant::Error(e.to_string())
    }
    pub fn iterator(i: impl VariantIter + 'static) -> Variant {
        Variant::Iterator(Box::new(i))
    }
    pub fn dict(v: &[(Variant, Variant)]) -> Variant {
        Variant::Dict(Box::new(v.iter().cloned().collect()))
    }
    pub fn native_fn(f: fn(&[Variant]) -> Variant) -> Variant {
        Variant::NativeFunc(NativeFunction::new(f))
    }

    pub fn func(args: Vec<Rc<str>>, body: Vec<Expression>) -> Variant {
        Variant::Func(Rc::new(Function::new(args, body)))
    }

    fn to_string_in_collection(&self) -> String {
        match self {
            Variant::Error(_) => format!("\"{self}\"",),
            Variant::Str(s) => format!("\"{s}\""),
            _ => self.to_string(),
        }
    }

    pub fn is_true(&self) -> Result<bool> {
        match self {
            Variant::Bool(b) => Ok(*b),
            a => Err(anyhow!("{a:?} is not a boolean")),
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            Variant::Int(i) => *i == 0,
            Variant::Float(f) => *f == 0.0,
            _ => false,
        }
    }

    pub fn add(&self, other: &Variant) -> Result<Variant> {
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => {
                return a
                    .checked_add(*b)
                    .map(Variant::Int)
                    .ok_or_else(|| anyhow!("Sum of {self:?} and {other:?} resulted in overflow"))
            }
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a + b),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float(*a as Float + b),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a + *b as Float),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::add)?,
            (Variant::Str(a), b) => {
                let mut c = a.clone();
                c.push_str(b.to_string().trim_matches('"'));
                Variant::Str(c)
            }
            (a, Variant::Str(b)) => {
                let mut c = a.to_string().trim_matches('"').to_string();
                c.push_str(b);
                Variant::Str(c)
            }
            _ => return Err(anyhow!("Cannot add {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn sub(&self, other: &Variant) -> Result<Variant> {
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => {
                return a
                    .checked_sub(*b)
                    .map(Variant::Int)
                    .ok_or_else(|| anyhow!("Sub of {self:?} and {other:?} resulted in overflow"))
            }
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a - b),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float(*a as Float - b),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a - *b as Float),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::sub)?,

            _ => return Err(anyhow!("Cannot sub {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn div(&self, other: &Variant) -> Result<Variant> {
        if other.is_zero() {
            return Err(anyhow!("Cannot divide by zero"));
        }
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Float(*a as Float / *b as Float),
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a / b),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float(*a as Float / b),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a / *b as Float),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::div)?,
            _ => return Err(anyhow!("Cannot div {self:?} and {other:?}")),
        };
        Ok(result)
    }

    fn div_exact(&self, other: &Variant) -> Result<Variant> {
        if other.is_zero() {
            return Err(anyhow!("Cannot divide by zero"));
        }
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Int(a / b),
            (Variant::Float(a), Variant::Float(b)) => Variant::Int(*a as Int / *b as Int),
            (Variant::Int(a), Variant::Float(b)) => Variant::Int(a / *b as Int),
            (Variant::Float(a), Variant::Int(b)) => Variant::Int(*a as Int / b),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::div_exact)?,
            _ => return Err(anyhow!("Cannot div_exact {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn mul(&self, other: &Variant) -> Result<Variant> {
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => {
                return a
                    .checked_mul(*b)
                    .map(Variant::Int)
                    .ok_or_else(|| anyhow!("Mul of {self:?} and {other:?} resulted in overflow"))
            }
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a * b),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float(*a as Float * b),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a * *b as Float),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::mul)?,
            (Variant::Str(a), &Variant::Int(b)) => {
                if b >= 0 {
                    Variant::Str(a.repeat(b as usize))
                } else {
                    return Err(anyhow!("Cannot multiply a string by a negative value"));
                }
            }
            _ => return Err(anyhow!("Cannot mul {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn rem(&self, other: &Variant) -> Result<Variant> {
        if other.is_zero() {
            return Err(anyhow!("Cannot divide by zero"));
        }
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Float(*a as Float % *b as Float),
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a % b),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float(*a as Float % b),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a % *b as Float),
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::rem)?,
            _ => return Err(anyhow!("Cannot rem {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn not(&self) -> Result<Variant> {
        match self {
            Variant::Bool(b) => Ok(Variant::Bool(!b)),
            _ => Err(anyhow!("Cannot apply NOT to {self:?}")),
        }
    }

    pub fn and(&self, other: &Variant) -> Result<Variant> {
        match (self, other) {
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::and),
            (&Variant::Bool(a), &Variant::Bool(b)) => Ok(Variant::Bool(a && b)),
            _ => Err(anyhow!("Cannot apply AND to {self:?} and {other:?}")),
        }
    }

    pub fn or(&self, other: &Variant) -> Result<Variant> {
        match (self, other) {
            (Variant::Vec(a), Variant::Vec(b)) => apply_op_between_vecs(a, b, Self::or),
            (&Variant::Bool(a), &Variant::Bool(b)) => Ok(Variant::Bool(a || b)),
            (a, b) => Err(anyhow!("Cannot apply OR to {a:?} and {b:?}")),
        }
    }

    pub fn neg(&self) -> Result<Variant> {
        match self {
            Variant::Int(i) => Ok(Variant::Int(-i)),
            Variant::Float(i) => Ok(Variant::Float(-i)),
            _ => Err(anyhow!("Cannot negate {self:?}")),
        }
    }

    fn is_indexable_guard(&self, index: &Variant) -> Result<()> {
        match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => {
                if i >= 0 {
                    a.get(i as usize)
                        .map(|_| ())
                        .ok_or_else(|| anyhow!("Index {i} out of bounds"))
                } else {
                    Err(anyhow!(
                        "Cannot index a vector with {i} because it is negative number"
                    ))
                }
            }

            (Variant::Vec(a), &Variant::Float(f)) => match f {
                _ if f < 0.0 => Err(anyhow!(
                    "Cannot index a vector with {f} because it is negative number"
                )),
                _ if f.fract() != 0.0 => Err(anyhow!(
                    "Cannot index a vector with {f} because it is an FP number"
                )),
                _ => a
                    .get(f as usize)
                    .map(|_| ())
                    .ok_or_else(|| anyhow!("Index {f} out of bounds")),
            },

            (Variant::Dict(a), _) => a
                .get(index)
                .map(|_| ())
                .ok_or_else(|| anyhow!("Key not found in dictionary")),

            (a, _) => Err(anyhow!("Cannot index {a:?}")),
        }
    }

    pub fn index(&self, index: &Variant) -> Result<&Variant> {
        self.is_indexable_guard(index)?;
        let reference = match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => a.get(i as usize).unwrap(),
            (Variant::Vec(a), &Variant::Float(f)) => a.get(f as usize).unwrap(),
            (Variant::Dict(a), _) => a.get(index).unwrap(),
            _ => unreachable!(),
        };
        Ok(reference)
    }

    pub fn index_mut(&mut self, index: &Variant) -> Result<&mut Variant> {
        self.is_indexable_guard(index)?;
        let reference = match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => a.get_mut(i as usize).unwrap(),
            (Variant::Vec(a), &Variant::Float(f)) => a.get_mut(f as usize).unwrap(),
            (Variant::Dict(a), _) => a
                .entry(index.clone())
                .or_insert(Variant::error("Uninitialized key")),
            _ => unreachable!(),
        };
        Ok(reference)
    }

    pub fn into_vec(self) -> Result<Variant> {
        match self {
            Variant::Dict(d) => Ok(Variant::Vec(
                d.into_iter()
                    .map(|(a, b)| Variant::Vec(vec![a, b]))
                    .collect(),
            )),
            Variant::Iterator(r) => Ok(Variant::Vec(r.clone().collect())),
            Variant::Vec(v) => Ok(Variant::Vec(v)),
            a => Err(anyhow!("Can't convert {a:?} to Vec")),
        }
    }

    fn into_pair(self) -> Result<(Variant, Variant)> {
        if self.len()? == 2 {
            if let Variant::Vec(v) = self {
                let first = v.get(0).unwrap().clone();
                let second = v.get(1).unwrap().clone();
                Ok((first, second))
            } else {
                Err(anyhow!(
                    "Can't convert {:?} to pair because it's not a Vec",
                    self
                ))
            }
        } else {
            Err(anyhow!(
                "Can't convert {:?} to pair because it doesnt have two elements",
                self
            ))
        }
    }

    fn into_dict(self) -> Result<Variant> {
        match self {
            Variant::Vec(v) => {
                let r: Result<Dictionary> = v.into_iter().map(|i| i.into_pair()).collect();
                Ok(Variant::Dict(Box::new(r?)))
            }
            Variant::Iterator(i) => {
                let r: Result<Dictionary> = i.map(|i| i.into_pair()).collect();
                Ok(Variant::Dict(Box::new(r?)))
            }
            Variant::Dict(d) => Ok(Variant::Dict(d)),
            a => Err(anyhow!("Can't convert {a:?} to dict")),
        }
    }

    pub fn into_iterator(self) -> Result<Variant> {
        match self {
            Variant::Str(s) => {
                let g: Vec<_> = s.graphemes(true).map(Variant::str).collect();
                Ok(Variant::iterator(g.into_iter()))
            }
            Variant::Vec(v) => Ok(Variant::iterator(v.into_iter())),
            Variant::Dict(d) => Ok(Variant::iterator(
                d.into_iter()
                    .map(|(k, v)| Variant::Vec(vec![k, v]))
                    .collect::<Vec<_>>()
                    .into_iter(),
            )),
            //Variant::Bytes(b) => Ok(Variant::iterator(b.into_iter().map(Variant::Byte))),
            Variant::Iterator(i) => Ok(Variant::Iterator(i)),

            a => Err(anyhow!("Can't convert {a:?} to iterator")),
        }
    }

    pub fn map(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?;
        match (iter, func) {
            (Variant::Iterator(i), Variant::NativeFunc(f)) => {
                Ok(Variant::iterator(i.map(move |i| f.call(&[i]))))
            }
            (Variant::Iterator(i), Variant::Func(f)) => {
                //TODO: Remove unwrap and allow access to global variables
                Ok(Variant::iterator(
                    i.map(move |i| f.call(&[i], &mut Memory::new()).unwrap()),
                ))
            }
            (i, Variant::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, Variant::Func(_)) => Err(anyhow!("Can't map {i:?} because it is not an iterator")),
            (Variant::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    pub fn filter(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?;
        match (iter, func) {
            (Variant::Iterator(i), Variant::NativeFunc(f)) => {
                let a = i.filter(move |j| match f.call(std::slice::from_ref(&j)) {
                    Variant::Bool(b) => b,
                    a => {
                        eprintln!("Warning: {a:?} it's not a boolean, interpreting it as false",);
                        false
                    }
                });
                Ok(Variant::iterator(a))
            }
            (Variant::Iterator(i), Variant::Func(f)) => {
                //TODO: Remove unwrap and allow access to global variables
                let a = i.filter(move |j| {
                    match (f.call(std::slice::from_ref(j), &mut Memory::new())).unwrap() {
                        Variant::Bool(b) => b,
                        a => {
                            eprintln!(
                                "Warning: {a:?} it's not a boolean, interpreting it as false",
                            );
                            false
                        }
                    }
                });
                Ok(Variant::iterator(a))
            }

            (i, Variant::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, Variant::Func(_)) => Err(anyhow!("Can't map {i:?} because it is not an iterator")),
            (Variant::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    pub fn reduce(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?;
        match (iter, func) {
            (Variant::Iterator(i), Variant::NativeFunc(f)) => {
                match i.reduce(move |acc, x| f.call(&[acc, x])) {
                    Some(j) => Ok(j),
                    None => Ok(Variant::error("Empty iterator")),
                }
            }
            //TODO: Remove unwrap and allow access to global variables
            (Variant::Iterator(i), Variant::Func(f)) => {
                match i.reduce(move |acc, x| f.call(&[acc, x], &mut Memory::new()).unwrap()) {
                    Some(j) => Ok(j),
                    None => Ok(Variant::error("Empty iterator")),
                }
            }
            (i, Variant::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, Variant::Func(_)) => Err(anyhow!("Can't map {i:?} because it is not an iterator")),
            (Variant::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    fn push(&mut self, element: Variant) -> Result<()> {
        match self {
            Variant::Vec(v) => {
                v.push(element);
                Ok(())
            }
            _ => Err(anyhow!("Can't push {element:?} to {self:?}")),
        }
    }

    fn insert(&mut self, key: Variant, value: Variant) -> Result<Option<Variant>> {
        match self {
            Variant::Dict(d) => Ok(d.insert(key, value)),
            _ => Err(anyhow!("Can't push ({key:?},{value:?}) in {self:?}")),
        }
    }

    fn len(&self) -> Result<usize> {
        let l = match self {
            //Variant::Bytes(b) => b.len(),
            Variant::Vec(v) => v.len(),
            Variant::Str(s) => s.graphemes(true).count(),
            Variant::Dict(d) => d.len(),
            Variant::Regex(r) => r.as_str().len(),
            _ => return Err(anyhow!("{self:?} doesn't have a lenght attribute")),
        };
        Ok(l)
    }
}

#[cfg(test)]
mod tests {
    use regex::Regex;
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    use crate::variant::{Dictionary, Variant};
    #[test]
    fn string_addition() {
        let a = Variant::str("hello");
        let b = Variant::str(" world");
        assert_eq!(Variant::str("hello world"), a.add(&b).unwrap());
        assert_eq!(a, Variant::str("hello"));
        assert_eq!(b, Variant::str(" world"));
    }

    #[test]
    fn variant_format() {
        let s = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::Vec(vec![Variant::Int(3), Variant::str("string")]),
            Variant::str("hello"),
        ])
        .to_string();
        assert_eq!(&s, r#"[1, 2, true, [3, "string"], "hello"]"#)
    }
    #[test]
    fn dictionary() {
        let bt = Variant::dict(&[
            (Variant::str("hola"), Variant::Int(5)),
            (Variant::str("zuelo"), Variant::Float(3.1)),
            (
                Variant::Vec(vec![Variant::Int(3), Variant::str("string")]),
                Variant::str("agua"),
            ),
            (
                Variant::Vec(vec![
                    Variant::Int(1),
                    Variant::Float(2.4),
                    Variant::error("error"),
                ]),
                Variant::error("error"),
            ),
            (Variant::Bool(true), Variant::Bool(true)),
            (Variant::Bool(false), Variant::Bool(true)),
            (Variant::error("error"), Variant::str("str")),
            (Variant::Float(3.1), Variant::error("error")),
            (Variant::Float(4.1), Variant::error("error")),
            (Variant::Int(4), Variant::str("int4")),
            (Variant::Int(3), Variant::str("int3")),
        ]);
        let a = bt.index(&Variant::error("error")).unwrap();
        assert_eq!(*a, Variant::str("str"))
    }
    #[test]
    fn comp_int_float() {
        assert_eq!(Variant::Float(1.0), Variant::Int(1));
    }

    #[test]
    fn index_vector() {
        let var = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::Vec(vec![Variant::Int(3), Variant::str("string")]),
            Variant::str("hello"),
        ]);
        assert_eq!(*var.index(&Variant::Int(2)).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn index_mut_vector() {
        let mut var = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::Vec(vec![Variant::Int(3)]),
            Variant::str("hello"),
        ]);
        *var.index_mut(&Variant::Float(4.)).unwrap() = Variant::error("Empty value");
        assert_eq!(
            &var.to_string(),
            "[1, 2, true, [3], \"Error: Empty value\"]"
        );
    }

    #[test]
    fn tag() {
        let v = [
            Variant::Error("".to_string()),
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::Byte(0),
            //Variant::Bytes(vec![]),
            Variant::Vec(vec![]),
            Variant::Str("string".to_string()),
            Variant::Dict(Box::new(Dictionary::default())),
            Variant::Regex(Regex::new("a").unwrap()),
        ]
        .map(|i| i.get_tag());
        assert_eq!([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], v);
    }

    #[test]
    fn to_dict_to_vec() {
        let v1 = Variant::Vec(vec![
            Variant::Vec(vec![Variant::default(), Variant::Int(0)]),
            Variant::Vec(vec![Variant::Int(1), Variant::Int(1)]),
            Variant::Vec(vec![Variant::Float(2.0), Variant::Int(2)]),
            Variant::Vec(vec![Variant::str("s"), Variant::Int(3)]),
        ]);
        assert_eq!(v1, v1.clone().into_dict().unwrap().into_vec().unwrap())
    }

    #[test]
    fn size_of_variant() {
        assert_eq!(std::mem::size_of::<Variant>(), 8)
    }

    #[test]
    fn hash_dictionary() {
        fn calculate_hash<T: Hash>(t: &T) -> u64 {
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        let mut a = Variant::dict(&[(Variant::Int(1), Variant::str("hola"))]);

        let mut b = Variant::dict(&[(Variant::Int(1), Variant::str("hola"))]);

        a.insert(Variant::Float(4.0), Variant::default()).unwrap();
        b.insert(Variant::Float(4.0), Variant::default()).unwrap();

        assert_eq!(calculate_hash(&a), calculate_hash(&b))
    }

    #[test]
    fn iterator_map() {
        let var = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .map(Variant::native_fn(|i| {
                i[0].add(&Variant::str("a")).unwrap()
            }))
            .unwrap()
            .into_vec()
            .unwrap();
        assert_eq!(
            a,
            Variant::Vec(vec![
                Variant::str("1a"),
                Variant::str("2a"),
                Variant::str("truea"),
                Variant::str("helloa")
            ])
        );
    }
    #[test]
    fn iterator_filter() {
        let var = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .filter(Variant::native_fn(|i| {
                Variant::Bool(match i[0] {
                    Variant::Int(_) => true,
                    _ => false,
                })
            }))
            .unwrap()
            .into_vec()
            .unwrap();
        assert_eq!(a, Variant::Vec(vec![Variant::Int(1),]));
    }

    #[test]
    fn iterator_reduce() {
        let var = Variant::Vec(vec![
            Variant::str("hello"),
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .reduce(Variant::native_fn(|i| i[0].add(&i[1]).unwrap()))
            .unwrap();
        assert_eq!(a, Variant::str("hello12true"));
    }

    #[test]
    fn filter_map_reduce() {
        let var = Variant::Vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .map(Variant::native_fn(|i| Variant::str(i[0].clone())))
            .unwrap()
            .filter(Variant::native_fn(|i| {
                Variant::Bool(match &i[0] {
                    Variant::Str(s) => s.parse::<f64>().is_ok(),
                    _ => false,
                })
            }))
            .unwrap()
            .reduce(Variant::native_fn(|i| {
                i[0].add(&i[1]).unwrap_or_else(Variant::error)
            }))
            .unwrap();
        assert_eq!(a, Variant::str("12"));
    }
}
