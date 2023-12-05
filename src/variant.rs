use crate::{
    expression::Expression,
    function::{Function, NativeFunction},
    iterator::VariantIterator,
    memory::Memory,
    shared::Shared,
};
use ahash::RandomState;
use anyhow::{anyhow, bail, Result};
use bstr::{BString, ByteSlice, ByteVec};
use derive_more::{IsVariant, Unwrap};
use dyn_clone::DynClone;
use indexmap::IndexMap;
use itertools::Itertools;
use std::{
    cell::{Ref, RefMut},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug + DynClone {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug + DynClone {}
dyn_clone::clone_trait_object!(VariantIter);

pub(crate) type Int = i64;
pub(crate) type Float = f64;
pub(crate) type Dictionary = IndexMap<Variant, Variant, RandomState>;

#[derive(Debug, Clone, IsVariant, Unwrap)]
#[repr(u8)]
pub enum Variant {
    Error(Rc<str>),
    Int(Int),
    Float(Float),
    Bool(bool),
    Byte(u8),
    Vec(Shared<Vec<Variant>>),
    Str(Rc<BString>),
    Dict(Shared<Dictionary>),
    Iterator(Shared<VariantIterator>),
    NativeFunc(Rc<NativeFunction>),
    Func(Rc<Function>),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Type {
    Int,
    Float,
    Bool,
    Byte,
    Vec,
    Str,
    Dict,
    Iterator,
    NativeFunc,
    Func,
    Error,
    Unit,
}

impl Default for Variant {
    fn default() -> Self {
        Variant::error("Uninitialized value")
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
            (Variant::Str(a), Variant::Str(b)) => a.cmp(b),
            (Variant::Dict(a), Variant::Dict(b)) => a.borrow().iter().cmp(b.borrow().iter()),
            (Variant::Vec(a), Variant::Vec(b)) => a.cmp(b),
            (Variant::Iterator(a), Variant::Iterator(b)) => a.as_ptr().cmp(&b.as_ptr()),
            (Variant::NativeFunc(a), Variant::NativeFunc(b)) => (a.name).cmp(&b.name),
            (Variant::Func(a), Variant::Func(b)) => a.cmp(b),
            (a, b) => a.get_type().cmp(&b.get_type()),
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
            (Variant::Iterator(a), Variant::Iterator(b)) => a.as_ptr() == b.as_ptr(),
            (Variant::NativeFunc(a), Variant::NativeFunc(b)) => Rc::ptr_eq(a, b),
            (Variant::Func(a), Variant::Func(b)) => a == b,
            (Variant::Unit, Variant::Unit) => true,
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
            Variant::Str(s) => write!(fmt, "{}", s.as_bstr()),
            Variant::Error(e) => write!(fmt, "Error: {e}"),
            Variant::Vec(v) => {
                let content = v
                    .borrow()
                    .iter()
                    .map(Variant::to_string_in_collection)
                    .join(", ");
                write!(fmt, "[{content}]")
            }
            Variant::Dict(d) => {
                let content = d
                    .borrow()
                    .iter()
                    .map(|(v1, v2)| {
                        let s1 = v1.to_string_in_collection();
                        let s2 = v2.to_string_in_collection();
                        format!("    {s1} : {s2}")
                    })
                    .join(", \n");
                write!(fmt, "{{\n{content}\n}}")
            }
            Variant::Func(a) => write!(fmt, "{a}"),
            Variant::Byte(b) => write!(fmt, "\\{:#01x}", b),
            Variant::Iterator(i) => write!(fmt, "{}", i.borrow()),
            Variant::NativeFunc(f) => write!(fmt, "{f}"),
            Variant::Unit => write!(fmt, "Unit"),
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
            Variant::Vec(a) => a.borrow().hash(state),
            Variant::Dict(a) => a.borrow().iter().for_each(|i| i.hash(state)),
            Variant::Func(f) => f.hash(state),
            Variant::Byte(b) => b.hash(state),
            Variant::Iterator(a) => a.as_ptr().hash(state),
            Variant::NativeFunc(f) => Rc::as_ptr(f).hash(state),
            Variant::Unit => 0_u8.hash(state),
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
    Ok(Variant::vec(result))
}

impl Variant {
    pub fn get_type(&self) -> Type {
        match self {
            Variant::Int(_) => Type::Int,
            Variant::Float(_) => Type::Float,
            Variant::Bool(_) => Type::Bool,
            Variant::Byte(_) => Type::Byte,
            Variant::Vec(_) => Type::Vec,
            Variant::Str(_) => Type::Str,
            Variant::Dict(_) => Type::Dict,
            Variant::Iterator(_) => Type::Iterator,
            Variant::NativeFunc(_) => Type::NativeFunc,
            Variant::Func(_) => Type::Func,
            Variant::Error(_) => Type::Error,
            Variant::Unit => Type::Unit,
        }
    }
    pub fn vec(v: Vec<Variant>) -> Variant {
        Variant::Vec(Shared::new(v))
    }

    pub fn str(s: impl ToString) -> Variant {
        Variant::Str(Rc::new(s.to_string().into()))
    }

    pub fn error(e: impl ToString) -> Variant {
        Variant::Error(e.to_string().into())
    }
    pub fn iterator(i: impl VariantIter + 'static) -> Variant {
        Variant::Iterator(Shared::new(VariantIterator::new(i)))
    }
    pub fn dict(v: &[(Variant, Variant)]) -> Variant {
        Variant::Dict(Shared::new(v.iter().cloned().collect()))
    }
    pub fn native_fn(
        name: Option<&str>,
        f: impl Fn(&[Variant], &mut Memory) -> Variant + 'static,
    ) -> Variant {
        if let Some(n) = name {
            Variant::NativeFunc(Rc::new(NativeFunction::new(n, f)))
        } else {
            Variant::NativeFunc(Rc::new(NativeFunction::anonymous(f)))
        }
    }

    pub fn method(
        name: &str,
        f: impl Fn(&[Variant], &mut Memory) -> Variant + 'static,
        method_of: Vec<Type>,
    ) -> Variant {
        Variant::NativeFunc(Rc::new(NativeFunction::method(name, f, method_of)))
    }

    pub fn anonymous_func(args: Vec<Rc<str>>, body: Vec<Expression>) -> Variant {
        Variant::Func(Rc::new(Function::anonymous(args, body)))
    }
    pub fn func(name: &str, args: Vec<Rc<str>>, body: Vec<Expression>) -> Variant {
        Variant::Func(Rc::new(Function::new(name, args, body)))
    }

    fn to_string_in_collection(&self) -> String {
        match self {
            Variant::Error(_) => format!("\"{self}\"",),
            Variant::Str(s) => format!("\"{}\"", s.as_bstr()),
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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::add)?
            }
            (Variant::Str(a), b) => {
                let mut c = (**a).as_bstr().to_owned();
                c.push_str(b.to_string().trim_matches('"'));
                Variant::Str(Rc::from(c))
            }
            (a, Variant::Str(b)) => {
                let mut c: BString = a.to_string().trim_matches('"').to_string().into();
                c.push_str(b.as_bstr());
                Variant::str(c)
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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::sub)?
            }

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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::div)?
            }
            _ => return Err(anyhow!("Cannot div {self:?} and {other:?}")),
        };
        Ok(result)
    }

    pub fn div_exact(&self, other: &Variant) -> Result<Variant> {
        if other.is_zero() {
            return Err(anyhow!("Cannot divide by zero"));
        }
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Int(a / b),
            (Variant::Float(a), Variant::Float(b)) => Variant::Int(*a as Int / *b as Int),
            (Variant::Int(a), Variant::Float(b)) => Variant::Int(a / *b as Int),
            (Variant::Float(a), Variant::Int(b)) => Variant::Int(*a as Int / b),
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::div_exact)?
            }
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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::mul)?
            }
            (Variant::Str(a), &Variant::Int(b)) => {
                if b >= 0 {
                    Variant::str(a.repeat(b as usize).as_bstr())
                } else {
                    return Err(anyhow!("Cannot multiply a string by a negative value"));
                }
            }
            _ => return Err(anyhow!("Cannot mul {self} and {other}")),
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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::rem)?
            }
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
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::and)
            }
            (&Variant::Bool(a), &Variant::Bool(b)) => Ok(Variant::Bool(a && b)),
            _ => Err(anyhow!("Cannot apply AND to {self:?} and {other:?}")),
        }
    }

    pub fn or(&self, other: &Variant) -> Result<Variant> {
        match (self, other) {
            (Variant::Vec(a), Variant::Vec(b)) => {
                apply_op_between_vecs(&a.borrow(), &b.borrow(), Self::or)
            }
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

    fn is_indexable_guard(&self, index: &Variant, mutable: bool) -> Result<()> {
        match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => {
                if i >= 0 {
                    a.borrow()
                        .get(i as usize)
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
                    .borrow()
                    .get(f as usize)
                    .map(|_| ())
                    .ok_or_else(|| anyhow!("Index {f} out of bounds")),
            },

            (Variant::Dict(a), _) => {
                if mutable {
                    Ok(())
                } else {
                    a.borrow()
                        .get(index)
                        .map(|_| ())
                        .ok_or_else(|| anyhow!("Key not found in dictionary"))
                }
            }

            (a, _) => Err(anyhow!("Cannot index {a:?}")),
        }
    }

    pub fn index(&self, index: &Variant) -> Result<Ref<Variant>> {
        self.is_indexable_guard(index, false)?;
        let reference = match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => {
                Ref::map(a.borrow(), |v| v.get(i as usize).unwrap())
            }
            (Variant::Vec(a), &Variant::Float(f)) => {
                Ref::map(a.borrow(), |v| v.get(f as usize).unwrap())
            }
            (Variant::Dict(a), _) => Ref::map(a.borrow(), |v| v.get(index).unwrap()),
            _ => unreachable!(),
        };
        Ok(reference)
    }

    pub fn index_mut(&mut self, index: &Variant) -> Result<RefMut<Variant>> {
        self.is_indexable_guard(index, true)?;
        let reference = match (self, index) {
            (Variant::Vec(a), &Variant::Int(i)) => {
                RefMut::map(a.borrow_mut(), |v| v.get_mut(i as usize).unwrap())
            }
            (Variant::Vec(a), &Variant::Float(f)) => {
                RefMut::map(a.borrow_mut(), |v| v.get_mut(f as usize).unwrap())
            }
            (Variant::Dict(a), _) => RefMut::map(a.borrow_mut(), |v| {
                v.entry(index.clone())
                    .or_insert(Variant::error("Uninitialized key"))
            }),
            _ => unreachable!(),
        };
        Ok(reference)
    }

    pub fn into_vec(self, memory: &mut Memory) -> Result<Variant> {
        match self {
            Variant::Dict(d) => Ok(Variant::vec(
                d.borrow()
                    .iter()
                    .map(|(a, b)| Variant::vec(vec![a.clone(), b.clone()]))
                    .collect(),
            )),
            Variant::Iterator(r) => Ok(r.borrow_mut().clone().to_variant_vec(memory)),
            Variant::Vec(v) => Ok(Variant::Vec(v)),
            a => Err(anyhow!("Can't convert {a:?} to Vec")),
        }
    }

    pub fn into_pair(&self) -> Result<(Variant, Variant)> {
        if self.len()? != 2 {
            bail!("Can't convert {self:?} to pair because it doesnt have two elements",)
        }
        if let Variant::Vec(v) = self {
            let first = v.borrow().get(0).unwrap().clone();
            let second = v.borrow().get(1).unwrap().clone();
            Ok((first, second))
        } else {
            bail!("Can't convert {self:?} to pair because it's not a Vec")
        }
    }

    pub fn into_dict(self, memory: &mut Memory) -> Result<Variant> {
        match self {
            Variant::Vec(v) => {
                let r: Result<Dictionary> =
                    v.borrow().iter().map(|i| i.clone().into_pair()).collect();
                Ok(Variant::Dict(Shared::new(r?)))
            }
            Variant::Iterator(i) => {
                let r = i.borrow_mut().clone().to_dict(memory);
                Ok(Variant::Dict(Shared::new(r?)))
            }
            Variant::Dict(d) => Ok(Variant::Dict(d)),
            a => Err(anyhow!("Can't convert {a:?} to dict")),
        }
    }

    pub fn into_iterator(self) -> Result<Variant> {
        match self {
            Variant::Str(s) => {
                let i = s.to_vec().into_iter();
                Ok(Variant::iterator(i.map(Variant::Byte)))
            }
            Variant::Vec(v) => Ok(Variant::iterator(
                v.unwrap_or_clone().into_inner().into_iter(),
            )),
            Variant::Dict(d) => Ok(Variant::iterator(
                d.borrow()
                    .iter()
                    .map(|(k, v)| Variant::vec(vec![k.clone(), v.clone()]))
                    .collect::<Vec<_>>()
                    .into_iter(),
            )),
            Variant::Iterator(i) => Ok(Variant::Iterator(i)),

            a => bail!("Can't convert {a:?} to iterator"),
        }
    }

    pub fn push(&mut self, element: Variant) -> Result<()> {
        match self {
            Variant::Vec(v) => {
                v.borrow_mut().push(element);
                Ok(())
            }
            _ => Err(anyhow!("Can't push {element:?} to {self:?}")),
        }
    }

    pub fn insert(&mut self, key: Variant, value: Variant) -> Result<Option<Variant>> {
        match self {
            Variant::Dict(d) => Ok(d.borrow_mut().insert(key, value)),
            _ => Err(anyhow!("Can't push ({key:?},{value:?}) in {self:?}")),
        }
    }

    pub fn len(&self) -> Result<usize> {
        let l = match self {
            Variant::Vec(v) => v.borrow().len(),
            Variant::Str(s) => s.len(),
            Variant::Dict(d) => d.borrow().len(),
            _ => return Err(anyhow!("{self:?} doesn't have a lenght attribute")),
        };
        Ok(l)
    }

    pub fn call(&self, args: &[Variant], memory: &mut Memory) -> Result<Variant> {
        match self {
            Variant::NativeFunc(f) => Ok(f.call(args, memory)),
            Variant::Func(f) => f.call(args, memory),
            _ => Err(anyhow!("{self} it is not callable")),
        }
    }
}

#[cfg(test)]
mod tests {
    use bstr::ByteSlice;
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    use crate::{
        memory::Memory,
        variant::{Type, Variant},
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
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::vec(vec![Variant::Int(3), Variant::str("string")]),
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
                Variant::vec(vec![Variant::Int(3), Variant::str("string")]),
                Variant::str("agua"),
            ),
            (
                Variant::vec(vec![
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
        let var = Variant::vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::vec(vec![Variant::Int(3), Variant::str("string")]),
            Variant::str("hello"),
        ]);
        assert_eq!(*var.index(&Variant::Int(2)).unwrap(), Variant::Bool(true));
    }

    #[test]
    fn index_mut_vector() {
        let mut var = Variant::vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::vec(vec![Variant::Int(3)]),
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
            Variant::error(""),
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::Byte(0),
            Variant::vec(vec![]),
            Variant::str("string"),
            Variant::dict(&[]),
        ]
        .map(|i| i.get_type());
        assert_eq!(
            [
                Type::Error,
                Type::Int,
                Type::Float,
                Type::Bool,
                Type::Byte,
                Type::Vec,
                Type::Str,
                Type::Dict
            ],
            v
        );
    }

    #[test]
    fn to_dict_to_vec() {
        let memory = &mut Memory::new();
        let v1 = Variant::vec(vec![
            Variant::vec(vec![Variant::default(), Variant::Int(0)]),
            Variant::vec(vec![Variant::Int(1), Variant::Int(1)]),
            Variant::vec(vec![Variant::Float(2.0), Variant::Int(2)]),
            Variant::vec(vec![Variant::str("s"), Variant::Int(3)]),
        ]);
        assert_eq!(
            v1,
            v1.clone()
                .into_dict(memory)
                .unwrap()
                .into_vec(memory)
                .unwrap()
        )
    }

    #[test]
    fn size_of_variant() {
        assert_eq!(std::mem::size_of::<Variant>(), 24)
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
        let memory = &mut Memory::new();
        let var = Variant::vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .unwrap_iterator()
            .borrow_mut()
            .map(Variant::native_fn(None, |i, _| {
                i[0].add(&Variant::str("a")).unwrap()
            }))
            .clone()
            .to_variant_vec(memory);
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
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);
        let memory = &mut Memory::new();
        let a = var
            .into_iterator()
            .unwrap()
            .unwrap_iterator()
            .borrow_mut()
            .filter(Variant::native_fn(None, |i, _| {
                Variant::Bool(match i[0] {
                    Variant::Int(_) => true,
                    _ => false,
                })
            }))
            .clone()
            .to_variant_vec(memory);
        assert_eq!(a, Variant::vec(vec![Variant::Int(1),]));
    }

    #[test]
    fn iterator_reduce() {
        let var = Variant::vec(vec![
            Variant::str("hello"),
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .unwrap_iterator()
            .borrow_mut()
            .clone()
            .reduce(
                &Variant::native_fn(None, |i, _| i[0].add(&i[1]).unwrap()),
                &mut Memory::new(),
            )
            .unwrap();
        assert_eq!(a, Variant::str("hello12true"));
    }

    #[test]
    fn filter_map_reduce() {
        let var = Variant::vec(vec![
            Variant::Int(1),
            Variant::Float(2.0),
            Variant::Bool(true),
            Variant::str("hello"),
        ]);

        let a = var
            .into_iterator()
            .unwrap()
            .unwrap_iterator()
            .borrow_mut()
            .map(Variant::native_fn(None, |i, _| Variant::str(i[0].clone())))
            .filter(Variant::native_fn(None, |i, _| {
                Variant::Bool(match &i[0] {
                    Variant::Str(s) => s.to_str_lossy().parse::<f64>().is_ok(),
                    _ => false,
                })
            }))
            .clone()
            .reduce(
                &Variant::native_fn(None, |i, _| i[0].add(&i[1]).unwrap_or_else(Variant::error)),
                &mut Memory::new(),
            )
            .unwrap();
        assert_eq!(a, Variant::str("12"));
    }
}
