use std::rc::Rc;
use std::cell::RefCell;

struct Shared<T> {
    value: Rc<RefCell<T>>,
}

impl<T> Shared<T> {
    fn new(value: T) -> Self {
        Shared {
            value: Rc::new(RefCell::new(value)),
        }
    }

    fn borrow(&self) -> std::cell::Ref<T> {
        self.value.borrow()
    }

    fn borrow_mut(&self) -> std::cell::RefMut<T> {
        self.value.borrow_mut()
    }
}

use qcell::{TCell, TCellOwner};

pub struct Marker;
pub type ACell<T> = TCell<Marker, T>;
pub type ACellOwner = TCellOwner<Marker>;
#[derive(Clone)]
pub struct Shared2<T>(Rc<ACell<T>>);

impl<T> Shared2<T> {
    fn borrow<'a>(&'a self, owner: &'a ACellOwner) -> &'a T {
        owner.ro(&self.0)
    }

    fn borrow_mut<'a>(&'a self, owner: &'a mut ACellOwner) -> &'a T {
        owner.rw(&self.0)
    }

    fn new(value: T) -> Self {
        Shared2(Rc::new(ACell::new(value)))
    }

    fn into_inner(self) -> T {
        Rc::try_unwrap(self.0).ok().unwrap().into_inner()
    }
}

