//! # Broom
//!
//! An ergonomic tracing garbage collector that supports mark 'n sweep garbage collection.
//!
//! ## Example
//!
//! ```
//! use broom::prelude::*;
//!
//! // The type you want the heap to contain
//! pub enum Object {
//!     Num(f64),
//!     List(Vec<Handle<Self>>),
//! }
//!
//! // Tell the garbage collector how to explore a graph of this object
//! impl Trace<Self> for Object {
//!     fn trace(&self, tracer: &mut Tracer<Self>) {
//!         match self {
//!             Object::Num(_) => {},
//!             Object::List(objects) => objects.trace(tracer),
//!         }
//!     }
//! }
//!
//! // Create a new heap
//! let mut heap = Heap::default();
//!
//! // Temporary objects are cheaper than rooted objects, but don't survive heap cleans
//! let a = heap.insert_temp(Object::Num(42.0));
//! let b = heap.insert_temp(Object::Num(1337.0));
//!
//! // Turn the numbers into a rooted list
//! let c = heap.insert(Object::List(vec![a, b]));
//!
//! // Change one of the numbers - this is safe, even if the object is self-referential!
//! heap.mutate(a, |a| *a = Object::Num(256.0));
//!
//! // Create another number object
//! let d = heap.insert_temp(Object::Num(0.0));
//!
//! // Clean up unused heap objects
//! heap.clean();
//!
//! // a, b and c are all kept alive because c is rooted and a and b are its children
//! assert!(heap.contains(a));
//! assert!(heap.contains(b));
//! assert!(heap.contains(c));
//!
//! // Because `d` was temporary and unused, it did not survive the heap clean
//! assert!(!heap.contains(d));
//!
//! ```

pub mod trace;

use std::rc::Rc;
use hashbrown::{HashMap, HashSet};

pub mod prelude {
    pub use super::{
        Heap,
        Handle,
        Rooted,
        trace::{Trace, Tracer},
    };
}

use trace::*;

/// A heap through which objects may be stored, accessed and mutated.
///
/// [`Heap`] is the centre of `broom`'s universe. It's the singleton through with manipulation of
/// objects occurs. It can be used to create, access, mutate and garbage-collect objects.
pub struct Heap<T> {
    last_sweep: usize,
    object_sweeps: HashMap<*mut T, usize>,
    objects: HashSet<*mut T>,
    rooted: HashMap<*mut T, Rc<()>>,
}

impl<T> Default for Heap<T> {
    fn default() -> Self {
        Self {
            last_sweep: 0,
            object_sweeps: HashMap::default(),
            objects: HashSet::default(),
            rooted: HashMap::default(),
        }
    }
}

impl<T: Trace<T>> Heap<T> {
    /// Adds a new object that will be cleared upon the next garbage collection, if not attached
    /// to the object tree.
    pub fn insert_temp(&mut self, object: T) -> Handle<T> {
        let ptr = Box::into_raw(Box::new(object));

        self.objects.insert(ptr);

        Handle { ptr }
    }

    /// Adds a new object that will not be cleared by garbage collection until all rooted handles
    /// have been dropped.
    pub fn insert(&mut self, object: T) -> Rooted<T> {
        let handle = self.insert_temp(object);

        let rc = Rc::new(());
        self.rooted.insert(handle.ptr, rc.clone());

        Rooted {
            rc,
            handle,
        }
    }

    /// Upgrade a handle (that will be cleared by the garbage collector) into a rooted handle (that
    /// will not).
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

    /// Count the number of heap-allocated objects in this heap
    pub fn len(&self) -> usize {
        self.objects.len()
    }

    /// Return true if the heap contains the specified handle
    pub fn contains(&self, handle: impl AsRef<Handle<T>>) -> bool {
        let handle = handle.as_ref();
        self.objects.contains(&handle.ptr)
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
        //debug_assert!(self.contains(handle));
        &*handle.ptr
    }

    /// Mutate a heap object
    ///
    // Because it's impossible to mutably (or immutably) access this [`Heap`] from within the
    // closure, it's safe for this to mutate a single object since accessing the [`Heap`] is the
    // only way to turn a handle to an object into an actual reference.
    pub fn mutate<R, F: FnOnce(&mut T) -> R>(&mut self, handle: impl AsRef<Handle<T>>, f: F) -> Option<R> {
        let handle = handle.as_ref();
        if self.contains(handle) {
            Some(f(unsafe { &mut *handle.ptr }))
        } else {
            None
        }
    }

    /// Mutate a heap object without first checking that it is still alive or that it belongs to
    /// this heap.
    ///
    /// If either invariant is not upheld, calling this function results in undefined
    /// behaviour.
    pub unsafe fn mutate_unchecked<R, F: FnOnce(&mut T) -> R>(&mut self, handle: impl AsRef<Handle<T>>, f: F) -> R {
        let handle = handle.as_ref();
        //debug_assert!(self.contains(handle));
        f(&mut *handle.ptr)
    }

    /// Clean orphaned objects from the heap, excluding those that can be reached from the given
    /// handle iterator.
    pub fn clean_excluding(&mut self, excluding: impl IntoIterator<Item=Handle<T>>) {
        let new_sweep = self.last_sweep + 1;
        let mut tracer = Tracer {
            new_sweep,
            object_sweeps: &mut self.object_sweeps,
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
        let objects = &self.objects;
        excluding
            .into_iter()
            .filter(|handle| objects.contains(&handle.ptr))
            .for_each(|handle| {
                tracer.mark(handle);
                unsafe { &*handle.ptr }.trace(&mut tracer);
            });

        // Sweep
        let object_sweeps = &mut self.object_sweeps;
        self.objects
            .retain(|ptr| {
                if object_sweeps
                    .get(ptr)
                    .map(|sweep| *sweep == new_sweep)
                    .unwrap_or(false)
                {
                    true
                } else {
                    object_sweeps.remove(ptr);
                    drop(unsafe { Box::from_raw(*ptr) });
                    false
                }
            });

        self.last_sweep = new_sweep;
    }

    /// Clean orphaned objects from the heap.
    pub fn clean(&mut self) {
        self.clean_excluding(std::iter::empty());
    }
}

impl<T> Drop for Heap<T> {
    fn drop(&mut self) {
        for ptr in &self.objects {
            drop(unsafe { Box::from_raw(*ptr) });
        }
    }
}

/// A handle to a heap object.
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

/// A handle to a heap object that guarantees the object will not be cleaned up by the garbage
/// collector.
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

    impl Trace<Self> for Value {
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
