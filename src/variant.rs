#![allow(dead_code)]
#![allow(unstable_name_collisions)]
#![allow(non_snake_case)]

use crate::{
    expression::Expression,
    function::{Function, NativeFunction},
    number::{Int, Number},
};
use ahash::RandomState;
use anyhow::{anyhow, Result};
use dyn_clone::DynClone;
use indexmap::IndexMap;
use itertools::Itertools;
use regex::Regex;
use std::{
    cell::{Ref, RefCell, RefMut},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, Neg},
    rc::Rc,
};
use unicode_segmentation::UnicodeSegmentation;

type Dictionary = IndexMap<Variant, Variant, RandomState>;
pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug + DynClone {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug + DynClone {}

dyn_clone::clone_trait_object!(VariantIter);
#[derive(Debug, Clone)]
pub enum VariantEnum {
    Error(String),
    Number(Number),
    Bool(bool),
    Byte(u8),
    Bytes(Vec<u8>),
    Vec(Vec<Variant>),
    Str(String),
    Dict(Dictionary),
    Regex(Regex),
    Iterator(Box<dyn VariantIter>),
    NativeFunc(NativeFunction),
    Func(Function),
}

impl Default for VariantEnum {
    fn default() -> Self {
        VariantEnum::Error("Uninitialized value".to_string())
    }
}

impl Ord for VariantEnum {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (VariantEnum::Error(a), VariantEnum::Error(b)) => a.cmp(b),
            (&VariantEnum::Number(a), VariantEnum::Number(b)) => a.cmp(b),
            (&VariantEnum::Bool(a), VariantEnum::Bool(b)) => a.cmp(b),
            (&VariantEnum::Byte(a), VariantEnum::Byte(b)) => a.cmp(b),
            (VariantEnum::Bytes(a), VariantEnum::Bytes(b)) => a.cmp(b),
            (VariantEnum::Str(a), VariantEnum::Str(b)) => a.cmp(b),
            (VariantEnum::Dict(a), VariantEnum::Dict(b)) => a.iter().cmp(b.iter()),
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => a.cmp(b),
            (VariantEnum::Regex(a), VariantEnum::Regex(b)) => a.as_str().cmp(b.as_str()),
            (VariantEnum::Iterator(a), VariantEnum::Iterator(b)) => a.clone().cmp(b.clone()),
            (VariantEnum::NativeFunc(a), VariantEnum::NativeFunc(b)) => {
                (a as *const _ as usize).cmp(&(b as *const _ as usize))
            }
            (VariantEnum::Func(a), VariantEnum::Func(b)) => a.cmp(b),
            (a, b) => a.get_tag().cmp(&b.get_tag()),
        }
    }
}

impl PartialOrd for VariantEnum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for VariantEnum {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => a == b,
            (&VariantEnum::Bool(a), &VariantEnum::Bool(b)) => a == b,
            (VariantEnum::Error(a), VariantEnum::Error(b)) => a == b,
            (&VariantEnum::Byte(a), &VariantEnum::Byte(b)) => a == b,
            (VariantEnum::Bytes(a), VariantEnum::Bytes(b)) => a == b,
            (VariantEnum::Str(a), VariantEnum::Str(b)) => a == b,
            (VariantEnum::Dict(a), VariantEnum::Dict(b)) => a == b,
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => a == b,
            (VariantEnum::Regex(a), VariantEnum::Regex(b)) => a.as_str() == b.as_str(),
            (VariantEnum::Iterator(a), VariantEnum::Iterator(b)) => a.clone().eq(b.clone()),
            (VariantEnum::NativeFunc(a), VariantEnum::NativeFunc(b)) => {
                (a as *const _ as usize).eq(&(b as *const _ as usize))
            }
            (VariantEnum::Func(a), VariantEnum::Func(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for VariantEnum {}

impl VariantEnum {
    fn get_tag(&self) -> u8 {
        unsafe { *(self as *const _ as *const u8) }
    }
}

impl fmt::Display for VariantEnum {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VariantEnum::Bool(b) => write!(fmt, "{b}"),
            VariantEnum::Number(n) => write!(fmt, "{n}"),
            VariantEnum::Str(s) => write!(fmt, "{s}"),
            VariantEnum::Error(e) => write!(fmt, "Error: {e}"),
            VariantEnum::Vec(v) => {
                let content: String = v
                    .iter()
                    .map(Variant::to_string_in_collection)
                    .intersperse(", ".to_string())
                    .collect();
                write!(fmt, "[{}]", content)
            }
            VariantEnum::Dict(d) => {
                let content: String = d
                    .iter()
                    .map(|(v1, v2)| {
                        let s1 = v1.to_string_in_collection();
                        let s2 = v2.to_string_in_collection();
                        format!("{} : {}", s1, s2)
                    })
                    .intersperse(", ".to_string())
                    .collect();
                write!(fmt, "{{{}}}", content)
            }
            VariantEnum::Func(a) => write!(fmt, "Function at {:#X}", a as *const _ as usize),
            VariantEnum::Bytes(v) => {
                let s: String = v.iter().map(|b| format!("\\{:#01x}", b)).collect();
                write!(fmt, "{}", s)
            }
            VariantEnum::Byte(b) => write!(fmt, "\\{:#01x}", b),
            VariantEnum::Regex(r) => write!(fmt, "{}", r.as_str()),
            VariantEnum::Iterator(i) => write!(fmt, "{i:?}"),
            VariantEnum::NativeFunc(f) => {
                write!(fmt, "Native function at {:?}", f as *const _)
            }
        }
    }
}
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd, Default)]
pub struct Variant(pub Rc<RefCell<VariantEnum>>);

impl fmt::Debug for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0.borrow())
        } else {
            write!(f, "{:?}", self.0.borrow())
        }
    }
}

impl Hash for Variant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &*self.0.borrow() {
            VariantEnum::Error(e) => {
                0_u8.hash(state);
                e.hash(state)
            }
            VariantEnum::Number(a) => a.hash(state),
            VariantEnum::Bool(a) => a.hash(state),
            VariantEnum::Str(a) => a.hash(state),
            VariantEnum::Vec(a) => a.hash(state),
            VariantEnum::Dict(a) => a.iter().for_each(|i| i.hash(state)),
            VariantEnum::Func(f) => f.hash(state),
            VariantEnum::Bytes(v) => v.hash(state),
            VariantEnum::Byte(b) => b.hash(state),
            VariantEnum::Regex(r) => r.as_str().hash(state),
            VariantEnum::Iterator(a) => a.clone().for_each(|i| i.hash(state)),
            VariantEnum::NativeFunc(f) => (&f as *const _ as usize).hash(state),
        };
    }
}

impl fmt::Display for Variant {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", self.0.borrow())
    }
}

use std::ops::Add;

impl Add for Variant {
    type Output = Result<Variant>;
    fn add(self, other: Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a + b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::add)?,
            (VariantEnum::Str(a), b) => {
                let mut c = a.clone();
                c.push_str(b.to_string().trim_matches('"'));
                Variant::str(c)
            }
            (a, VariantEnum::Str(b)) => {
                let mut c = a.to_string().trim_matches('"').to_string();
                c.push_str(b);
                Variant::str(c)
            }
            _ => return Err(anyhow!("Cannot add {self:?} and {other:?}")),
        };
        Ok(result)
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
    Ok(Variant::vec(result))
}

impl Variant {
    pub fn unwrap_or_clone(self) -> VariantEnum {
        Rc::try_unwrap(self.0)
            .unwrap_or_else(|arc| (*arc).clone())
            .into_inner()
    }
    pub fn new(value: VariantEnum) -> Self {
        Variant(Rc::new(RefCell::new(value)))
    }
    pub fn str(s: impl ToString) -> Variant {
        Variant::new(VariantEnum::Str(s.to_string()))
    }
    pub fn vec(v: Vec<Variant>) -> Variant {
        Variant::new(VariantEnum::Vec(v))
    }

    pub fn float(f: f64) -> Variant {
        Variant::new(VariantEnum::Number(Number::Float(f)))
    }

    pub fn int(i: Int) -> Variant {
        Variant::new(VariantEnum::Number(Number::Int(i)))
    }
    pub fn bool(b: bool) -> Variant {
        Variant::new(VariantEnum::Bool(b))
    }
    pub fn error(e: impl ToString) -> Variant {
        Variant::new(VariantEnum::Error(e.to_string()))
    }
    pub fn iterator(i: impl VariantIter + 'static) -> Variant {
        Variant::new(VariantEnum::Iterator(Box::new(i)))
    }
    pub fn dict(v: &[(Variant, Variant)]) -> Variant {
        Variant::new(VariantEnum::Dict(v.iter().cloned().collect()))
    }
    pub fn native_fn(f: fn(&[Variant]) -> Variant) -> Variant {
        Variant::new(VariantEnum::NativeFunc(NativeFunction::new(f)))
    }

    pub fn func(args: Vec<String>, body: Vec<Expression>) -> Variant {
        Variant::new(VariantEnum::Func(Function::new(args, body)))
    }

    fn to_string_in_collection(&self) -> String {
        match &*self.0.borrow() {
            VariantEnum::Error(_) => format!("\"{}\"", self.to_string()),
            VariantEnum::Str(s) => format!("\"{}\"", s),
            _ => self.to_string(),
        }
    }

    pub fn is_true(&self) -> Result<bool> {
        match &*self.0.borrow() {
            VariantEnum::Bool(b) => Ok(*b),
            a => Err(anyhow!("{a:?} is not a boolean")),
        }
    }

    pub fn add(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a + b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::add)?,
            (VariantEnum::Str(a), b) => {
                let mut c = a.clone();
                c.push_str(b.to_string().trim_matches('"'));
                Variant::str(c)
            }
            (a, VariantEnum::Str(b)) => {
                let mut c = a.to_string().trim_matches('"').to_string();
                c.push_str(b);
                Variant::str(c)
            }
            _ => return Err(anyhow!("Cannot add {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn sub(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a - b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::sub)?,

            _ => return Err(anyhow!("Cannot sub {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn div(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a / b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::div)?,
            _ => return Err(anyhow!("Cannot div {self:?} and {other:?}")),
        };
        Ok(result)
    }

    fn div_exact(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a.div_exact(b)))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => {
                apply_op_between_vecs(a, b, Self::div_exact)?
            }
            _ => return Err(anyhow!("Cannot div_exact {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn mul(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a * b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::mul)?,
            (VariantEnum::Str(a), &VariantEnum::Number(b)) if b.is_int() => {
                let b = b.into_int();
                if b >= 0 {
                    Variant::str(a.repeat(b as usize))
                } else {
                    return Err(anyhow!("Cannot multiply a string by a negative value"));
                }
            }
            _ => return Err(anyhow!("Cannot mul {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn rem(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a % b))
            }
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::rem)?,
            _ => return Err(anyhow!("Cannot rem {self:?} and {other:?}")),
        };
        Ok(result)
    }

    fn pow(&self, other: &Variant) -> Result<Variant> {
        let result = match (&*self.0.borrow(), &*other.0.borrow()) {
            (&VariantEnum::Number(a), &VariantEnum::Number(b)) => {
                Variant::new(VariantEnum::Number(a.pow(b)))
            }
            _ => return Err(anyhow!("Cannot elevate {self:?} to {other:?}")),
        };
        Ok(result)
    }

    pub fn not(&self) -> Result<Variant> {
        match &*self.0.borrow() {
            VariantEnum::Bool(b) => Ok(Variant::bool(!b)),
            _ => Err(anyhow!("Cannot apply NOT to {self:?}")),
        }
    }

    pub fn and(&self, other: &Variant) -> Result<Variant> {
        match (&*self.0.borrow(), &*other.0.borrow()) {
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::and),
            (&VariantEnum::Bool(a), &VariantEnum::Bool(b)) => Ok(Variant::bool(a && b)),
            _ => Err(anyhow!("Cannot apply AND to {self:?} and {other:?}")),
        }
    }

    pub fn or(&self, other: &Variant) -> Result<Variant> {
        match (&*self.0.borrow(), &*other.0.borrow()) {
            (VariantEnum::Vec(a), VariantEnum::Vec(b)) => apply_op_between_vecs(a, b, Self::or),
            (&VariantEnum::Bool(a), &VariantEnum::Bool(b)) => Ok(Variant::bool(a || b)),
            (a, b) => Err(anyhow!("Cannot apply OR to {a:?} and {b:?}")),
        }
    }

    pub fn neg(&self) -> Result<Variant> {
        match &*self.0.borrow() {
            VariantEnum::Number(i) => Ok(Variant::new(VariantEnum::Number(i.neg()))),
            _ => Err(anyhow!("Cannot negate {self:?}")),
        }
    }

    fn is_indexable_guard(&self, index: &Variant) -> Result<()> {
        let container = &*self.0.borrow();
        let index_enum = &*index.0.borrow();
        match (container, index_enum) {
            (VariantEnum::Vec(a), &VariantEnum::Number(i)) if i.is_int() => {
                let i = i.into_int();
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

            (VariantEnum::Vec(a), &VariantEnum::Number(i)) if i.is_float() => match i {
                _ if i.into_float() < 0.0 => Err(anyhow!(
                    "Cannot index a vector with {i} because it is negative number"
                )),
                _ if i.into_float().fract() != 0.0 => Err(anyhow!(
                    "Cannot index a vector with {i} because it is an FP number"
                )),
                _ => a
                    .get(i.into_float() as usize)
                    .map(|_| ())
                    .ok_or_else(|| anyhow!("Index {i} out of bounds")),
            },

            (VariantEnum::Dict(a), _) => a
                .get(index)
                .map(|_| ())
                .ok_or_else(|| anyhow!("Key not found in dictionary")),

            (a, _) => Err(anyhow!("Cannot index {a:?}")),
        }
    }

    pub fn index(&self, index: &Variant) -> Result<Ref<'_, Variant>> {
        self.is_indexable_guard(index)?;
        let reference = Ref::map(self.0.borrow(), |container| {
            match (container, &*index.0.borrow()) {
                (VariantEnum::Vec(a), &VariantEnum::Number(i)) => {
                    a.get(i.into_int() as usize).unwrap()
                }
                (VariantEnum::Dict(a), _) => a.get(index).unwrap(),
                _ => unreachable!(),
            }
        });
        Ok(reference)
    }

    pub fn index_mut(&mut self, index: &Variant) -> Result<RefMut<'_, Variant>> {
        self.is_indexable_guard(index)?;
        let reference = RefMut::map(self.0.borrow_mut(), |container| {
            match (container, &*index.0.borrow()) {
                (VariantEnum::Vec(a), &VariantEnum::Number(i)) => {
                    a.get_mut(i.into_int() as usize).unwrap()
                }

                (VariantEnum::Dict(a), _) => a
                    .entry(index.clone())
                    .or_insert(Variant::error("Uninitialized key")),
                _ => unreachable!(),
            }
        });
        Ok(reference)
    }

    pub fn into_vec(self) -> Result<Variant> {
        match self.unwrap_or_clone() {
            VariantEnum::Dict(d) => Ok(Variant::vec(
                d.into_iter()
                    .map(|(a, b)| Variant::vec(vec![a.clone(), b.clone()]))
                    .collect(),
            )),
            VariantEnum::Iterator(r) => Ok(Variant::vec(r.clone().collect())),
            VariantEnum::Vec(v) => Ok(Variant::vec(v)),
            a => Err(anyhow!("Can't convert {a:?} to Vec")),
        }
    }

    fn into_pair(self) -> Result<(Variant, Variant)> {
        if self.len()? == 2 {
            if let VariantEnum::Vec(v) = self.0.borrow().deref() {
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
        match self.unwrap_or_clone() {
            VariantEnum::Vec(v) => {
                let r: Result<Vec<_>> = v.into_iter().map(|i| i.into_pair()).collect();
                Ok(Variant::dict(&r?))
            }
            VariantEnum::Iterator(i) => {
                let r: Result<Dictionary> = i.map(|i| i.into_pair()).collect();
                Ok(Variant::new(VariantEnum::Dict(r?)))
            }
            VariantEnum::Dict(d) => Ok(Variant::new(VariantEnum::Dict(d))),
            a => Err(anyhow!("Can't convert {a:?} to dict")),
        }
    }

    pub fn into_iterator(self) -> Result<Variant> {
        match self.unwrap_or_clone() {
            VariantEnum::Str(s) => {
                let g: Vec<_> = s.graphemes(true).map(Variant::str).collect();
                Ok(Variant::iterator(g.into_iter()))
            }
            VariantEnum::Vec(v) => Ok(Variant::iterator(v.into_iter())),
            VariantEnum::Dict(d) => Ok(Variant::iterator(
                d.into_iter()
                    .map(|(k, v)| Variant::vec(vec![k, v]))
                    .collect::<Vec<_>>()
                    .into_iter(),
            )),
            VariantEnum::Bytes(b) => Ok(Variant::iterator(
                b.into_iter().map(|i| Variant::new(VariantEnum::Byte(i))),
            )),
            VariantEnum::Iterator(i) => Ok(Variant::iterator(i)),

            a => Err(anyhow!("Can't convert {a:?} to iterator")),
        }
    }

    pub fn map(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?.unwrap_or_clone();
        match (iter, func.unwrap_or_clone()) {
            (VariantEnum::Iterator(i), VariantEnum::NativeFunc(f)) => {
                Ok(Variant::iterator(i.map(move |i| f.call(&[i]))))
            }
            (VariantEnum::Iterator(i), VariantEnum::Func(f)) => {
                //TODO: Remove unwrap and allow access to global variables
                Ok(Variant::iterator(
                    i.map(move |i| f.call(&[i], &mut vec![]).unwrap()),
                ))
            }
            (i, VariantEnum::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, VariantEnum::Func(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (VariantEnum::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    pub fn filter(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?.unwrap_or_clone();
        match (iter, func.unwrap_or_clone()) {
            (VariantEnum::Iterator(i), VariantEnum::NativeFunc(f)) => {
                let a =
                    i.filter(
                        move |j| match (f.call(std::slice::from_ref(j))).unwrap_or_clone() {
                            VariantEnum::Bool(b) => b,
                            a => {
                                eprintln!(
                                    "Warning: {a:?} it's not a boolean, interpreting it as false",
                                );
                                false
                            }
                        },
                    );
                Ok(Variant::iterator(a))
            }
            (VariantEnum::Iterator(i), VariantEnum::Func(f)) => {
                //TODO: Remove unwrap and allow access to global variables
                let a = i.filter(move |j| {
                    match (f.call(std::slice::from_ref(j), &mut vec![]))
                        .unwrap()
                        .unwrap_or_clone()
                    {
                        VariantEnum::Bool(b) => b,
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

            (i, VariantEnum::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, VariantEnum::Func(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (VariantEnum::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    pub fn reduce(self, func: Variant) -> Result<Variant> {
        let iter = self.into_iterator()?.unwrap_or_clone();
        match (iter, func.unwrap_or_clone()) {
            (VariantEnum::Iterator(i), VariantEnum::NativeFunc(f)) => {
                match i.reduce(move |acc, x| f.call(&[acc, x])) {
                    Some(j) => Ok(j),
                    None => Ok(Variant::error("Empty iterator")),
                }
            }
            //TODO: Remove unwrap and allow access to global variables
            (VariantEnum::Iterator(i), VariantEnum::Func(f)) => {
                match i.reduce(move |acc, x| f.call(&[acc, x], &mut vec![]).unwrap()) {
                    Some(j) => Ok(j),
                    None => Ok(Variant::error("Empty iterator")),
                }
            }
            (i, VariantEnum::NativeFunc(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (i, VariantEnum::Func(_)) => {
                Err(anyhow!("Can't map {i:?} because it is not an iterator"))
            }
            (VariantEnum::Iterator(i), f) => {
                Err(anyhow!("Can't map {i:?} because {f:?} is not a function",))
            }
            _ => todo!(),
        }
    }

    fn push(&mut self, element: Variant) -> Result<()> {
        match &mut *self.0.borrow_mut() {
            VariantEnum::Vec(v) => {
                v.push(element);
                Ok(())
            }
            _ => Err(anyhow!("Can't push {element:?} to {self:?}")),
        }
    }

    fn insert(&mut self, key: Variant, value: Variant) -> Result<Option<Variant>> {
        match &mut *self.0.borrow_mut() {
            VariantEnum::Dict(d) => Ok(d.insert(key, value)),
            _ => Err(anyhow!("Can't push ({key:?},{value:?}) in {self:?}")),
        }
    }

    fn len(&self) -> Result<usize> {
        let l = match &*self.0.borrow() {
            VariantEnum::Bytes(b) => b.len(),
            VariantEnum::Vec(v) => v.len(),
            VariantEnum::Str(s) => s.graphemes(true).count(),
            VariantEnum::Dict(d) => d.len(),
            VariantEnum::Regex(r) => r.as_str().len(),
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

    use crate::{
        number::Number,
        variant::{Dictionary, Variant, VariantEnum},
    };
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
        let s = Variant::vec(vec![
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
            Variant::vec(vec![Variant::int(3), Variant::str("string")]),
            Variant::str("hello"),
        ])
        .to_string();
        assert_eq!(&s, r#"[1, 2, true, [3, "string"], "hello"]"#)
    }
    #[test]
    fn dictionary() {
        let bt = Variant::dict(&[
            (Variant::str("hola"), Variant::int(5)),
            (Variant::str("zuelo"), Variant::float(3.1)),
            (
                Variant::vec(vec![Variant::int(3), Variant::str("string")]),
                Variant::str("agua"),
            ),
            (
                Variant::vec(vec![
                    Variant::int(1),
                    Variant::float(2.4),
                    Variant::error("error"),
                ]),
                Variant::error("error"),
            ),
            (Variant::bool(true), Variant::bool(true)),
            (Variant::bool(false), Variant::bool(true)),
            (Variant::error("error"), Variant::str("str")),
            (Variant::float(3.1), Variant::error("error")),
            (Variant::float(4.1), Variant::error("error")),
            (Variant::int(4), Variant::str("int4")),
            (Variant::int(3), Variant::str("int3")),
        ]);
        let a = bt.index(&Variant::error("error")).unwrap();
        assert_eq!(*a, Variant::str("str"))
    }
    #[test]
    fn comp_int_float() {
        assert_eq!(Variant::float(1.0), Variant::int(1));
    }

    #[test]
    fn index_vector() {
        let var = Variant::vec(vec![
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
            Variant::vec(vec![Variant::int(3), Variant::str("string")]),
            Variant::str("hello"),
        ]);
        assert_eq!(*var.index(&Variant::int(2)).unwrap(), Variant::bool(true));
    }

    #[test]
    fn index_mut_vector() {
        let mut var = Variant::vec(vec![
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
            Variant::vec(vec![Variant::int(3)]),
            Variant::str("hello"),
        ]);
        *var.index_mut(&Variant::float(4.)).unwrap() = Variant::error("Empty value");
        assert_eq!(
            &var.to_string(),
            "[1, 2, true, [3], \"Error: Empty value\"]"
        );
    }

    #[test]
    fn tag() {
        let v = [
            VariantEnum::Error("".to_string()),
            VariantEnum::Number(Number::Int(1)),
            VariantEnum::Bool(true),
            VariantEnum::Byte(0),
            VariantEnum::Bytes(vec![]),
            VariantEnum::Vec(vec![]),
            VariantEnum::Str("string".to_string()),
            VariantEnum::Dict(Dictionary::default()),
            VariantEnum::Regex(Regex::new("a").unwrap()),
        ]
        .map(|i| i.get_tag());
        assert_eq!([0, 1, 2, 3, 4, 5, 6, 7, 8], v);
    }

    #[test]
    fn to_dict_to_vec() {
        let v1 = Variant::vec(vec![
            Variant::vec(vec![Variant::default(), Variant::int(0)]),
            Variant::vec(vec![Variant::int(1), Variant::int(1)]),
            Variant::vec(vec![Variant::float(2.0), Variant::int(2)]),
            Variant::vec(vec![Variant::str("s"), Variant::int(3)]),
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

        let mut a = Variant::dict(&[(Variant::int(1), Variant::str("hola"))]);

        let mut b = Variant::dict(&[(Variant::int(1), Variant::str("hola"))]);

        a.insert(Variant::float(4.0), Variant::default()).unwrap();
        b.insert(Variant::float(4.0), Variant::default()).unwrap();

        assert_eq!(calculate_hash(&a), calculate_hash(&b))
    }

    #[test]
    fn iterator_map() {
        let var = Variant::vec(vec![
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
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
            Variant::vec(vec![
                Variant::str("1a"),
                Variant::str("2a"),
                Variant::str("truea"),
                Variant::str("helloa")
            ])
        );
    }
    #[test]
    fn iterator_filter() {
        let var = Variant::vec(vec![
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .filter(Variant::native_fn(|i| {
                Variant::bool(match *i[0].0.borrow() {
                    VariantEnum::Number(i) if i.is_int() => true,
                    _ => false,
                })
            }))
            .unwrap()
            .into_vec()
            .unwrap();
        assert_eq!(a, Variant::vec(vec![Variant::int(1),]));
    }

    #[test]
    fn iterator_reduce() {
        let var = Variant::vec(vec![
            Variant::str("hello"),
            Variant::int(1),
            Variant::float(2.0),
            Variant::bool(true),
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
            .reduce(Variant::native_fn(|i| {
                i[0].add(&i[1]).unwrap_or_else(Variant::error)
            }))
            .unwrap();
        assert_eq!(a, Variant::str("12"));
    }
}
