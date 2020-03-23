# Broom

Broom is a simple, fast, and easy to use mark & sweep garbage collector for Rust.

## Features

- Simple API
- Mark and sweep heap cleaning
- Simple mutation of heap values
- Zero-cost access to heap items through handles

## Example

```rust
use broom::{Handle, Trace, Tracer, Heap};

// The type you want the heap to contain
pub enum Object {
    Num(f64),
    List(Vec<Handle<Self>>),
}

// Allow the garbage collector to explore the object graph
impl Trace for Object {
    fn trace(&self, tracer: &mut Tracer<Self>) {
        match self {
            Value::List(items) => items.trace(tracer),
            _ => {},
        }
    }
}

// Create a new heap
let mut heap = Heap::default();

// Creating temporary objects is cheaper than creating rooted objects.
// However, temporary objects are not saved from cleanups.
let a = heap.insert_temp(Object::Num(42.0));
let b = heap.insert_temp(Object::Num(1337.0));

// Turn the numbers into a rooted list
let c = heap.insert(Object::List(vec![
    a.handle(),
    b.handle(),
]));

// Change one of the numbers
heap.mutate(a, |a| *a = Object::Num(256.0));

// Clean up unused heap objects
heap.clean();

// a, b and c are all kept alive because c is rooted and a and b are its children
assert!(heap.contains(a), true);
assert!(heap.contains(b), true);
assert!(heap.contains(c), true);
```

## Who this crate is for

- People writing dynamically-typed languages in Rust that want a simple, reliable garbage collector
- People that want to have complex graph data structure with cycles and don't want memory leaks

## Who this crate is not for

- People that want garbage collection when writing ordinary Rust code
