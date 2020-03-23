use std::rc::Rc;
use hashbrown::{HashMap, HashSet};

pub mod prelude {
    pub use super::{
        Heap,
        Handle,
        Rooted,
    };
}

pub mod trace {
    use super::*;

    pub trait Trace: Sized {
        fn trace(&self, tracer: &mut Tracer<Self>);
    }

    pub struct Tracer<'a, T: Trace> {
        pub(crate) new_sweep: usize,
        pub(crate) item_sweeps: &'a mut HashMap<*mut T, usize>,
        pub(crate) items: &'a HashSet<*mut T>,
    }
}

use trace::*;

impl<'a, T: Trace> Tracer<'a, T> {
    pub fn mark(&mut self, handle: Handle<T>) {
        let sweep = self.item_sweeps
            .entry(handle.ptr)
            .or_insert(self.new_sweep - 1);
        if *sweep != self.new_sweep {
            *sweep = self.new_sweep;
            unsafe { &*handle.ptr }.trace(self);
        }
    }
}

pub struct Heap<T> {
    last_sweep: usize,
    item_sweeps: HashMap<*mut T, usize>,
    items: HashSet<*mut T>,
    rooted: HashMap<*mut T, Rc<()>>,
}

impl<T> Default for Heap<T> {
    fn default() -> Self {
        Self {
            last_sweep: 0,
            item_sweeps: HashMap::default(),
            items: HashSet::default(),
            rooted: HashMap::default(),
        }
    }
}

impl<T: Trace> Heap<T> {
    /// Adds a new item that will be cleared upon the next garbage collection, if not attached
    /// to the item tree.
    pub fn insert_temp(&mut self, item: T) -> Handle<T> {
        let ptr = Box::into_raw(Box::new(item));

        self.items.insert(ptr);

        Handle { ptr }
    }

    /// Adds a new item that will not be cleared by garbage collection until dropped.
    pub fn insert(&mut self, item: T) -> Rooted<T> {
        let handle = self.insert_temp(item);

        let rc = Rc::new(());
        self.rooted.insert(handle.ptr, rc.clone());

        Rooted {
            rc,
            handle,
        }
    }

    /// Turn the given handle into a rooted handle.
    pub fn make_rooted(&mut self, handle: impl AsRef<Handle<T>>) -> Rooted<T> {
        let handle = handle.as_ref();
        debug_assert!(self.contains(handle));

        Rooted {
            rc: self.rooted
                .entry(handle.ptr)
                .or_insert_with(|| Rc::new(()))
                .clone(),
            handle: *handle,
        }
    }

    /// Gives the number of heap-allocated items
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Return true if the heap contains the specified handle
    pub fn contains(&self, handle: impl AsRef<Handle<T>>) -> bool {
        let handle = handle.as_ref();
        self.items.contains(&handle.ptr)
    }

    // We can hand out immutable references as much as we like
    pub fn get(&self, handle: impl AsRef<Handle<T>>) -> Option<&T> {
        let handle = handle.as_ref();
        if self.contains(handle) {
            Some(unsafe { &*handle.ptr })
        } else {
            None
        }
    }

    // Undefined behaviour occurs when the handle does not originating in this heap.
    pub unsafe fn get_unchecked(&self, handle: impl AsRef<Handle<T>>) -> &T {
        let handle = handle.as_ref();
        debug_assert!(self.contains(handle));
        &*handle.ptr
    }

    // Because it's impossible to mutably (or immutably) access this `GcHeap` from within the
    // closure, it's safe for this to mutate a single item since accessing the `GcHeap` is the
    // only way to turn a handle to an item into an actual reference.
    pub fn mutate<R, F: FnOnce(&mut T) -> R>(&mut self, handle: impl AsRef<Handle<T>>, f: F) -> Option<R> {
        let handle = handle.as_ref();
        if self.contains(handle) {
            Some(f(unsafe { &mut *handle.ptr }))
        } else {
            None
        }
    }

    // Undefined behaviour occurs when the handle does not originating in this heap.
    pub unsafe fn mutate_unchecked<R, F: FnOnce(&mut T) -> R>(&mut self, handle: impl AsRef<Handle<T>>, f: F) -> R {
        let handle = handle.as_ref();
        debug_assert!(self.contains(handle));
        f(&mut *handle.ptr)
    }

    /// Clean orphaned items from the heap, excluding those that can be reached from the given handles.
    pub fn clean_excluding(&mut self, excluding: impl IntoIterator<Item=Handle<T>>) {
        let new_sweep = self.last_sweep + 1;
        let mut tracer = Tracer {
            new_sweep,
            item_sweeps: &mut self.item_sweeps,
            items: &self.items,
        };

        // Mark
        self.rooted
            .retain(|ptr, rc| {
                if Rc::strong_count(rc) > 1 {
                    tracer.mark(Handle { ptr: *ptr });
                    unsafe { &**ptr }.trace(&mut tracer);
                    true
                } else {
                    false
                }
            });
        let items = &self.items;
        excluding
            .into_iter()
            .filter(|handle| items.contains(&handle.ptr))
            .for_each(|handle| {
                tracer.mark(handle);
                unsafe { &*handle.ptr }.trace(&mut tracer);
            });

        // Sweep
        let item_sweeps = &mut self.item_sweeps;
        self.items
            .retain(|ptr| {
                if item_sweeps
                    .get(ptr)
                    .map(|sweep| *sweep == new_sweep)
                    .unwrap_or(false)
                {
                    true
                } else {
                    item_sweeps.remove(ptr);
                    drop(unsafe { Box::from_raw(*ptr) });
                    false
                }
            });

        self.last_sweep = new_sweep;
    }

    /// Clean orphaned items from the heap
    pub fn clean(&mut self) {
        self.clean_excluding(std::iter::empty());
    }
}

impl<T> Drop for Heap<T> {
    fn drop(&mut self) {
        for ptr in &self.items {
            drop(unsafe { Box::from_raw(*ptr) });
        }
    }
}

#[derive(Debug)]
pub struct Handle<T> {
    ptr: *mut T,
}

impl<T> Copy for Handle<T> {}
impl<T> Clone for Handle<T> {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr }
    }
}

impl<T> AsRef<Handle<T>> for Handle<T> {
    fn as_ref(&self) -> &Handle<T> {
        self
    }
}

impl<T> From<Rooted<T>> for Handle<T> {
    fn from(rooted: Rooted<T>) -> Self {
        rooted.handle
    }
}

#[derive(Debug)]
pub struct Rooted<T> {
    rc: Rc<()>,
    handle: Handle<T>,
}

impl<T> Clone for Rooted<T> {
    fn clone(&self) -> Self {
        Self {
            rc: self.rc.clone(),
            handle: self.handle,
        }
    }
}

impl<T> AsRef<Handle<T>> for Rooted<T> {
    fn as_ref(&self) -> &Handle<T> {
        &self.handle
    }
}

impl<T> Rooted<T> {
    pub fn into_handle(self) -> Handle<T> {
        self.handle
    }

    pub fn handle(&self) -> Handle<T> {
        self.handle
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    enum Value {
        Base,
        Refs(Handle<Value>, Handle<Value>),
    }

    impl Trace for Value {
        fn trace(&self, tracer: &mut Tracer<Self>) {
            match self {
                Value::Base => {},
                Value::Refs(a, b) => {
                    tracer.mark(*a);
                    tracer.mark(*b);
                },
            }
        }
    }

    #[test]
    fn basic() {
        let mut heap = Heap::default();

        let a = heap.insert(Value::Base);

        heap.clean();

        assert_eq!(heap.contains(&a), true);

        let a = a.into_handle();

        heap.clean();

        assert_eq!(heap.contains(&a), false);
    }

    #[test]
    fn ownership() {
        let mut heap = Heap::default();

        let a = heap.insert(Value::Base).handle();
        let b = heap.insert(Value::Base).handle();
        let c = heap.insert(Value::Base).handle();
        let d = heap.insert(Value::Refs(a, c));
        let e = heap.insert(Value::Base).handle();

        heap.clean();

        assert_eq!(heap.contains(&a), true);
        assert_eq!(heap.contains(&b), false);
        assert_eq!(heap.contains(&c), true);
        assert_eq!(heap.contains(&d), true);
        assert_eq!(heap.contains(&e), false);

        let a = heap.insert_temp(Value::Base);

        heap.clean();

        assert_eq!(heap.contains(&a), false);

        let a = heap.insert_temp(Value::Base);
        let a = heap.make_rooted(a);

        heap.clean();

        assert_eq!(heap.contains(&a), true);
    }

    #[test]
    fn recursive() {
        let mut heap = Heap::default();

        let a = heap.insert(Value::Base);
        let b = heap.insert(Value::Base);

        heap.mutate(&a, |a_val| *a_val = Value::Refs(a.handle(), b.handle()));

        heap.clean();

        assert_eq!(heap.contains(&a), true);
        assert_eq!(heap.contains(&b), true);

        let a = a.into_handle();

        heap.clean();

        assert_eq!(heap.contains(&a), false);
        assert_eq!(heap.contains(&b), true);
    }

    #[test]
    fn temporary() {
        let mut heap = Heap::default();

        let a = heap.insert_temp(Value::Base);

        heap.clean();

        assert_eq!(heap.contains(&a), false);

        let a = heap.insert_temp(Value::Base);
        let b = heap.insert(Value::Refs(a, a));

        heap.clean();

        assert_eq!(heap.contains(&a), true);
        assert_eq!(heap.contains(&b), true);

        let a = heap.insert_temp(Value::Base);

        heap.clean_excluding(Some(a));

        assert_eq!(heap.contains(&a), true);
    }
}
