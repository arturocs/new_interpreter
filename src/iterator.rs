use crate::{
    memory::Memory,
    shared::Shared,
    variant::{Dictionary, Int, Variant},
};
use anyhow::{Context, Result};
use dyn_clone::DynClone;
use itertools::Itertools;
use paste::paste;
use std::{cell::RefCell, fmt, slice};
pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug + DynClone {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug + DynClone {}
dyn_clone::clone_trait_object!(VariantIter);

#[derive(Debug, Clone)]
pub enum Adapter {
    Generator(Variant),
    Filter(Variant),
    Map(Variant),
    FlatMap(Variant),
    Zip(Variant),
    Flatten,
    Enumerate,
    StepBy(usize),
    Take(usize),
    Skip(usize),
}

impl fmt::Display for Adapter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Adapter::Generator(a) => write!(f, "Generator({a})"),
            Adapter::Filter(a) => write!(f, "Filter({a})"),
            Adapter::Map(a) => write!(f, "Map({a})"),
            Adapter::FlatMap(a) => write!(f, "FlatMap({a})"),
            Adapter::Zip(a) => write!(f, "Zip({a})"),
            Adapter::Flatten => write!(f, "Flatten"),
            Adapter::Enumerate => write!(f, "Enumerate"),
            Adapter::StepBy(a) => write!(f, "StepBy({a})"),
            Adapter::Take(a) => write!(f, "Take({a})"),
            Adapter::Skip(a) => write!(f, "Skip({a})"),
        }
    }
}
#[derive(Debug, Clone)]
pub struct VariantIterator {
    adapters: Vec<Adapter>,
    base: Box<dyn VariantIter>,
}

impl fmt::Display for VariantIterator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Iterator {{ base: {:?}, adapters: [ {} ] }}",
            self.base,
            self.adapters.iter().map(Adapter::to_string).join(", ")
        )
    }
}

fn call_helper(func: &Variant, args: &[Variant], memory: &RefCell<&mut Memory>) -> Variant {
    func.call(args, &mut memory.borrow_mut())
        .unwrap_or_else(Variant::error)
}

macro_rules! implement_adapters {
    ($func:ident,Variant) => {
        paste! {
            impl VariantIterator {
                pub fn[<$func:snake>](&mut self, value: Variant) -> &mut Self{
                    self.adapters.push(Adapter::$func(value));
                    self
                }
            }
        }
    };
    ($func:ident,usize) => {
        paste! {
            impl VariantIterator {
                pub fn[<$func:snake>](&mut self, value: Variant) -> &mut Self{
                    match value {
                        Variant::Int(i) => self.adapters.push(Adapter::$func(i as usize)),
                        Variant::Float(f) => self.adapters.push(Adapter::$func(f as usize)),
                        _ => panic!("{} error: {} is not a number",stringify!($func),value),
                    }
                    self
                }
            }
        }
    };

    ($func:ident) => {
        paste! {
            impl VariantIterator {
                pub fn[<$func:snake>](&mut self) -> &mut Self{
                    self.adapters.push(Adapter::$func);
                    self
                }
            }
        }
    };
}

implement_adapters!(Map, Variant);
implement_adapters!(Filter, Variant);
implement_adapters!(FlatMap, Variant);
implement_adapters!(Zip, Variant);
implement_adapters!(Flatten);
implement_adapters!(Enumerate);
implement_adapters!(StepBy, usize);
implement_adapters!(Take, usize);
implement_adapters!(Skip, usize);

macro_rules! apply_method_to_iter {
    ($it:expr,$memory:expr,$method:expr) => {{
        let mut base = $it.base;
        let mem = RefCell::new($memory);
        for a in $it.adapters.iter() {
            base = match a {
                Adapter::Generator(f) => {
                    Box::new(std::iter::from_fn(|| match call_helper(f, &[], &mem) {
                        Variant::Error(_) => None,
                        a => Some(a),
                    }))
                }
                Adapter::Map(f) => Box::new(base.map(|i| call_helper(f, &[i], &mem))),
                Adapter::Filter(f) => {
                    Box::new(
                        base.filter(|i| match call_helper(f, slice::from_ref(i), &mem) {
                            Variant::Bool(b) => b,
                            e => {
                                eprintln!(
                                    "Warning: {e} it's not a boolean, interpreting it as false",
                                );
                                false
                            }
                        }),
                    )
                }
                Adapter::Flatten => Box::new(
                    base.flat_map(|i| match i {
                        Variant::Iterator(j) => j
                            .borrow_mut()
                            .clone()
                            .to_vec(&mut mem.borrow_mut())
                            .into_iter(),
                        e => vec![Variant::error(format!(
                            "Flatten error: {e} is not an iterator"
                        ))]
                        .into_iter(),
                    })
                    .collect_vec()
                    .into_iter(),
                ),
                Adapter::Zip(other) => {
                    if let Ok(Variant::Iterator(it)) = other.clone().into_iterator() {
                        Box::new(
                            base.zip(it.borrow_mut().clone().to_vec(&mut mem.borrow_mut()))
                                .map(|(i, j)| Variant::vec(vec![i, j])),
                        )
                    } else {
                        Box::new(
                            vec![Variant::error(format!(
                                "Zip error: {other} is not an iterator"
                            ))]
                            .into_iter(),
                        )
                    }
                }
                Adapter::Enumerate => Box::new(
                    base.enumerate()
                        .map(|(i, it)| Variant::vec(vec![Variant::Int(i as i64), it])),
                ),
                Adapter::StepBy(step) => Box::new(base.step_by(*step)),
                Adapter::Take(t) => Box::new(base.take(*t)),
                Adapter::Skip(s) => Box::new(base.skip(*s)),
                Adapter::FlatMap(f) => Box::new(
                    base.flat_map(|i| match i {
                        Variant::Iterator(j) => j
                            .borrow_mut()
                            .clone()
                            .to_vec(&mut mem.borrow_mut())
                            .into_iter(),
                        e => vec![Variant::error(format!(
                            "FlatMap error: {e} is not an iterator"
                        ))]
                        .into_iter(),
                    })
                    .map(|i| call_helper(f, &[i], &mem))
                    .collect_vec()
                    .into_iter(),
                ),
            }
        }
        $method(base, &mem)
    }};
}

impl VariantIterator {
    pub fn new(i: impl VariantIter + 'static) -> Self {
        Self {
            adapters: Vec::with_capacity(5),
            base: Box::new(i),
        }
    }

    pub fn from_adapter(adapter: Adapter, i: impl VariantIter + 'static) -> Self {
        let mut adapters = vec![adapter];
        adapters.reserve(5);
        Self {
            adapters,
            base: Box::new(i),
        }
    }

    pub fn to_vec(self, memory: &mut Memory) -> Vec<Variant> {
        apply_method_to_iter!(self, memory, |i, _| Vec::from_iter(i))
    }

    pub fn to_variant_vec(self, memory: &mut Memory) -> Variant {
        Variant::vec(self.to_vec(memory))
    }

    pub fn to_dict(self, memory: &mut Memory) -> Result<Dictionary> {
        apply_method_to_iter!(self, memory, |i: Box<dyn VariantIter>, _| i
            .map(|j| j.into_pair())
            .collect())
    }

    pub fn to_variant_dict(self, memory: &mut Memory) -> Variant {
        let dict = self.to_dict(memory);
        match dict {
            Ok(d) => Variant::Dict(Shared::new(d)),
            Err(e) => Variant::error(e),
        }
    }

    pub fn reduce(self, func: &Variant, memory: &mut Memory) -> Result<Variant> {
        apply_method_to_iter!(
            self,
            memory,
            |i: Box<dyn VariantIter>, m: &RefCell<&mut Memory>| {
                i.reduce(|acc, x| {
                    func.call(&[acc, x], &mut m.borrow_mut())
                        .unwrap_or_else(Variant::error)
                })
                .context("Empty iterator")
            }
        )
    }

    pub fn sum(self, memory: &mut Memory) -> Result<Variant> {
        apply_method_to_iter!(self, memory, |i: Box<dyn VariantIter>, _| {
            i.reduce(|acc, x| acc.add(&x).unwrap_or_else(Variant::error))
                .context("Empty iterator")
        })
    }

    pub fn count(self, memory: &mut Memory) -> Variant {
        apply_method_to_iter!(self, memory, |i: Box<dyn VariantIter>, _| {
            Variant::Int(i.count() as Int)
        })
    }

    pub fn any(self, memory: &mut Memory) -> Variant {
        apply_method_to_iter!(self, memory, |mut i: Box<dyn VariantIter>, _| {
            Variant::Bool(i.any(|i| i.is_true().unwrap_or(false)))
        })
    }

    pub fn all(self, memory: &mut Memory) -> Variant {
        apply_method_to_iter!(self, memory, |mut i: Box<dyn VariantIter>, _| {
            Variant::Bool(i.all(|i| i.is_true().unwrap_or(false)))
        })
    }

    pub fn find(self, func: &Variant, memory: &mut Memory) -> Result<Variant> {
        apply_method_to_iter!(
            self,
            memory,
            |mut i: Box<dyn VariantIter>, m: &RefCell<&mut Memory>| {
                i.find(|i| {
                    func.call(slice::from_ref(i), &mut m.borrow_mut())
                        .unwrap_or_else(Variant::error)
                        .is_true()
                        .unwrap_or(false)
                })
                .context("Empty iterator")
            }
        )
    }

    pub fn for_each(self, func: &Variant, memory: &mut Memory) -> Variant {
        apply_method_to_iter!(
            self,
            memory,
            |i: Box<dyn VariantIter>, m: &RefCell<&mut Memory>| {
                i.for_each(|i| {
                    func.call(slice::from_ref(&i), &mut m.borrow_mut())
                        .unwrap_or_else(Variant::error);
                })
            }
        );
        Variant::Unit
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn size_of_iterator() {
        assert_eq!(std::mem::size_of::<VariantIterator>(), 40)
    }
}
