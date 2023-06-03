use crate::{
    memory::Memory,
    variant::{Dictionary, Variant},
};
use anyhow::{anyhow, Result};
use bstr::BString;
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
    Enumerate(usize),
    StepBy(usize),
    Take(usize),
    Skip(usize),
}
struct VariantIterator3 {
    adapters: Vec<Adapter>,
    base: BaseIterator,
}

fn apply_adapters(item: Variant, adapters: &[Adapter]) -> Option<Variant> {
    
    for i in adapters {
        match i {
            Adapter::Map(v) => todo!(),
            Adapter::Filter(_) => todo!(),
            Adapter::Flatten => todo!(),
            Adapter::Enumerate(_) => todo!(),
            Adapter::StepBy(_) => todo!(),
            Adapter::Take(_) => todo!(),
            Adapter::Skip(_) => todo!(),
        }
    }
    todo!()
}

impl Iterator for VariantIterator3 {
    // We can refer to this type using Self::Item
    type Item = Variant;

    fn next(&mut self) -> Option<Variant> {
        match self.base {
            BaseIterator::Vec(_) => todo!(),
            BaseIterator::Dict(_) => todo!(),
            BaseIterator::Range(_) => todo!(),
            BaseIterator::Str(_) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
