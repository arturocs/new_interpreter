use std::cell::RefCell;
use std::rc::Rc;
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Shared<T: Clone> {
    value: Rc<RefCell<T>>,
}

impl<T: Clone> Shared<T> {
    pub fn new(value: T) -> Self {
        Shared {
            value: Rc::new(RefCell::new(value)),
        }
    }

    pub fn borrow(&self) -> std::cell::Ref<T> {
        self.value.borrow()
    }

    pub fn borrow_mut(&self) -> std::cell::RefMut<T> {
        self.value.borrow_mut()
    }

    pub fn as_ptr(&self) -> *const T {
        self.value.as_ptr()
    }

    pub fn unwrap_or_clone(self) -> RefCell<T> {
        Rc::try_unwrap(self.value).unwrap_or_else(|rc| (*rc).clone())
    }
}
