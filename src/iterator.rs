use crate::{
    memory::Memory,
    variant::{Dictionary, Variant},
};
use anyhow::{Context, Result};
use dyn_clone::DynClone;
use itertools::Itertools;
use paste::paste;
use std::{cell::RefCell, fmt, rc::Rc, slice};
pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug + DynClone {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug + DynClone {}
dyn_clone::clone_trait_object!(VariantIter);

#[derive(Debug, Clone)]
pub enum Adapter {
    Filter(Variant),
    Map(Variant),
    FlatMap(Variant),
    Flatten,
    Enumerate,
    StepBy(usize),
    Take(usize),
    Skip(usize),
}

#[derive(Debug, Clone)]
pub struct VariantIterator {
    adapters: Vec<Adapter>,
    base: Box<dyn VariantIter>,
}

fn call_helper(func: &Variant, args: &[Variant], memory: &RefCell<&mut Memory>) -> Variant {
    func.call(args, &mut *memory.borrow_mut())
        .unwrap_or_else(|e| Variant::error(e))
}

macro_rules! implement_adapters {
    ($func:ident,$type:ty) => {
        paste! {impl VariantIterator {
            pub fn[<$func:snake>](&mut self, value: $type) {
                self.adapters.push(Adapter::$func(value));
            }
        }}
    };

    ($func:ident) => {
        paste! {impl VariantIterator {
            pub fn[<$func:snake>](&mut self) {
                self.adapters.push(Adapter::$func);
            }
        }}
    };
}

implement_adapters!(Map, Variant);
implement_adapters!(Filter, Variant);
implement_adapters!(FlatMap, Variant);
implement_adapters!(Flatten);
implement_adapters!(Enumerate);
implement_adapters!(StepBy, usize);
implement_adapters!(Take, usize);
implement_adapters!(Skip, usize);

impl VariantIterator {
    pub fn new(i: impl VariantIter + 'static) -> Self {
        Self {
            adapters: Vec::with_capacity(5),
            base: Box::new(i),
        }
    }

    pub fn to_vec(self, memory: &mut Memory) -> Vec<Variant> {
        let mut base = self.base;
        let mem = RefCell::new(memory);
        for a in self.adapters.iter() {
            base = match a {
                Adapter::Map(f) => Box::new(base.map(|i| call_helper(f, &[i], &mem))),
                Adapter::Filter(f) => {
                    Box::new(
                        base.filter(|i| match call_helper(f, slice::from_ref(i), &mem) {
                            Variant::Bool(b) => b,
                            e => {
                                eprintln!(
                                    "Warning: {e:?} it's not a boolean, interpreting it as false",
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
                            .to_vec(&mut *mem.borrow_mut())
                            .into_iter(),
                        e => vec![Variant::error(format!(
                            "Flatten error: {e:?} is not an iterator"
                        ))]
                        .into_iter(),
                    })
                    .collect_vec()
                    .into_iter(),
                ),
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
                            .to_vec(&mut *mem.borrow_mut())
                            .into_iter(),
                        e => vec![Variant::error(format!(
                            "FlatMap error: {e:?} is not an iterator"
                        ))]
                        .into_iter(),
                    })
                    .map(|i| call_helper(f, &[i], &mem))
                    .collect_vec()
                    .into_iter(),
                ),
            }
        }

        base.collect()
    }

    pub fn to_variant_vec(self, memory: &mut Memory) -> Variant {
        Variant::vec(self.to_vec(memory))
    }

    pub fn to_dict(self, memory: &mut Memory) -> Result<Dictionary> {
        self.to_vec(memory)
            .into_iter()
            .map(|i| {
                /* let Variant::Vec(v) = i else { return None };
                let first = v.borrow().get(0)?.clone();
                let second = v.borrow().get(1)?.clone();
                Some((first, second)) */
                i.into_pair(memory)
            })
            .collect()
    }

    pub fn to_variant_dict(self, memory: &mut Memory) -> Variant {
        let dict = self.to_dict(memory);
        match dict {
            Ok(d) =>  Variant::Dict(Rc::new(RefCell::new(d))),
            Err(e) => Variant::error(e),
        }
       
    }

    pub fn reduce(self, func: &Variant, memory: &mut Memory) -> Result<Variant> {
        self.to_vec(memory)
            .into_iter()
            .reduce(move |acc, x| func.call(&[acc, x], memory).unwrap_or_else(Variant::error))
            .context("Empty iterator")
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
