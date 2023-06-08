use crate::{
    memory::Memory,
    variant::{Dictionary, Variant},
};
use anyhow::{anyhow, Result};

use std::{cell::RefCell, fmt, rc::Rc};
pub trait VariantIter: Iterator<Item = Variant> + fmt::Debug {}
impl<T> VariantIter for T where T: Iterator<Item = Variant> + fmt::Debug {}

#[derive(Debug, Clone)]
pub struct VariantIterator(Rc<RefCell<dyn VariantIter>>);

impl Iterator for VariantIterator {
    type Item = Variant;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.borrow_mut().next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.borrow().size_hint()
    }
}

impl VariantIterator {
    pub fn new(i: impl VariantIter + 'static) -> Self {
        Self(Rc::new(RefCell::new(i)))
    }

    pub fn map2(self, func: Variant, memory: &'static mut Memory) -> Result<VariantIterator> {
        //let m = Rc::new(RefCell::new(memory));
        // let a = RefCell::new(1);
        // let b = a.borrow_mut();
        let result = match func {
            Variant::NativeFunc(f) => {
                let a = self.scan(memory,move |m,i| Some(f.call(&[i], m)))/* .map(move |i| f.call(&[i], memory)) */;
                VariantIterator::new(a)
            }
            /*      Variant::Func(f) => VariantIterator::new(self.map(move |i| {
                           f.call(&[i], &mut m.borrow_mut())
                               .unwrap_or_else(Variant::error)
                       })),
            */
            f => {
                return Err(anyhow!(
                    "Can't map {self:?} because {f:?} is not a function",
                ))
            }
        };
        Ok(result)
    }
}

#[derive(Debug)]
pub enum BaseIterator {
    Vec(std::vec::IntoIter<Variant>),
    Dict(indexmap::map::IntoIter<Variant, Variant>),
    Range(std::ops::Range<i64>),
    Str(std::vec::IntoIter<u8>),
}

pub enum VariantIterator2 {
    Base(BaseIterator),
    Map {
        iterator: Box<VariantIterator2>,
        function: Variant,
    },
    Filter {
        iterator: Box<VariantIterator2>,
        function: Variant,
    },
    Enumerate(Box<VariantIterator2>),
    Flatten(Box<VariantIterator2>),
    StepBy(Box<VariantIterator2>),
}

impl From<Vec<Variant>> for VariantIterator2 {
    fn from(base: Vec<Variant>) -> Self {
        VariantIterator2::Base(BaseIterator::Vec(base.into_iter()))
    }
}

impl VariantIterator2 {
    fn map(self, function: Variant) -> Self {
        let a = Dictionary::default();
        let b = a.into_iter();
        VariantIterator2::Map {
            iterator: Box::new(self),
            function,
        }
    }

    fn filter(self, function: Variant) -> Self {
        VariantIterator2::Filter {
            iterator: Box::new(self),
            function,
        }
    }

    fn reduce(self, function: Variant) -> Variant {
        todo!()
    }
}
#[derive(Debug)]
enum Adapter {
    Map(Variant),
    Filter(Variant),
    Flatten,
    Enumerate,
    StepBy(usize),
    Take(usize),
    Skip(usize),
}
struct VariantIterator3 {
    adapters: Vec<Adapter>,
    base: Box<dyn VariantIter>,
}

fn call_helper(func: &Variant, args: &[Variant], memory: &RefCell<&mut Memory>) -> Variant {
    func.call(args, &mut *memory.borrow_mut())
        .unwrap_or_else(|e| Variant::error(e))
}

impl VariantIterator3 {
    fn map(mut self, func: Variant) -> Self {
        self.adapters.push(Adapter::Map(func));
        self
    }

    fn to_vec(self, memory: &mut Memory) -> Variant {
        let mut base = self.base;
        let mem = RefCell::new(memory);
        for a in self.adapters.iter() {
            base = match a {
                Adapter::Map(f) => Box::new(base.map(|i| call_helper(f, &[i], &mem))),
                Adapter::Filter(f) => todo!(),
                Adapter::Flatten => Box::new(base.flatten()),
                Adapter::Enumerate => Box::new(
                    base.enumerate()
                        .map(|(i, it)| Variant::vec(vec![Variant::Int(i as i64), it])),
                ),
                Adapter::StepBy(step) => Box::new(base.step_by(*step)),
                Adapter::Take(t) => Box::new(base.take(*t)),
                Adapter::Skip(s) => Box::new(base.skip(*s)),
            }
        }

        Variant::vec(base.collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bstr::BString;
    #[test]
    fn size_of_expression() {
        assert_eq!(std::mem::size_of::<VariantIterator2>(), 72)
    }

    #[test]
    fn prueba() {
        let a = BString::from("Hello, world!");
        //let b = a.into_iter();
        assert_eq!(std::mem::size_of::<VariantIterator2>(), 72)
    }
}
