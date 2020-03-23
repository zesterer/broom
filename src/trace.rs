use super::*;

/// A trait used to tell the garbage collector how it may explore an object graph composed of
/// values of type `T`.
///
/// To implement this, simply call `foo.trace(tracer)` on all traceable children
/// of the type. Note that this trait has default implementations for a variety of common types.
///
/// # Example
/// ```
/// use broom::prelude::*;
///
/// pub enum Object {
///     Num(f64),
///     List(Vec<Handle<Self>>),
/// }
///
/// impl Trace<Self> for Object {
///     fn trace(&self, tracer: &mut Tracer<Self>) {
///         match self {
///             Object::Num(_) => {},
///             Object::List(objects) => objects.trace(tracer),
///         }
///     }
/// }
/// ```
pub trait Trace<T: Trace<T>> {
    /// Trace *all* child objects of this type.
    ///
    /// Note that although failing to trace all children is not undefined behaviour on its own, it
    /// will mean that objects may be accidentally garbage-collected, and hence that the
    /// `_unchecked` methods in this crate will produce undefined behaviour when used to access
    /// those objects.
    fn trace(&self, tracer: &mut Tracer<T>);
}

/// A type used to perform a heap trace. Largely an implementation detail: To implement heap
/// tracing, look at the [`Trace`] trait instead.
pub struct Tracer<'a, T: Trace<T>> {
    pub(crate) new_sweep: usize,
    pub(crate) object_sweeps: &'a mut HashMap<*mut T, usize>,
}

impl<'a, T: Trace<T>> Tracer<'a, T> {
    pub(crate) fn mark(&mut self, handle: Handle<T>) {
        let sweep = self.object_sweeps
            .entry(handle.ptr)
            .or_insert(self.new_sweep - 1);
        if *sweep != self.new_sweep {
            *sweep = self.new_sweep;
            unsafe { &*handle.ptr }.trace(self);
        }
    }
}

impl<O: Trace<O>> Trace<O> for Handle<O> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        tracer.mark(*self);
    }
}

impl<O: Trace<O>> Trace<O> for Rooted<O> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.handle().trace(tracer);
    }
}

// Impl on standard things
use std::collections::{
    HashMap as StdHashMap,
    VecDeque,
    LinkedList,
};

impl<O: Trace<O>, T: Trace<O>> Trace<O> for [T] {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.iter().for_each(|object| object.trace(tracer));
    }
}

impl<O: Trace<O>, T: Trace<O>> Trace<O> for VecDeque<T> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.iter().for_each(|object| object.trace(tracer));
    }
}

impl<O: Trace<O>, T: Trace<O>> Trace<O> for LinkedList<T> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.iter().for_each(|object| object.trace(tracer));
    }
}

impl<O: Trace<O>, K, V: Trace<O>> Trace<O> for StdHashMap<K, V> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.values().for_each(|object| object.trace(tracer));
    }
}

impl<O: Trace<O>, T: Trace<O>> Trace<O> for HashSet<T> {
    fn trace(&self, tracer: &mut Tracer<O>) {
        self.iter().for_each(|object| object.trace(tracer));
    }
}
