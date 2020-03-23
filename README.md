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

// Allow the garbage collector to explore the object tree
impl Trace for Object {
    fn trace(&self, tracer: &mut Tracer<Self>) {
        match self {
            Value::List(items) => items
                .iter()
                .for_each(|item| tracer.mark(*item)),
            _ => {},
        }
    }
}

// Create a new heap
let mut heap = Heap::default();

// Create a list of two numbers on the heap
let a = heap.insert(Object::Num(42.0));
let b = heap.insert(Object::Num(1337.0));
let c = heap.insert(Object::List(vec![
    a.handle(),
    b.handle(),
]));

// Change one of the numbers
heap.mutate(a, |a| *a = Object::Num(256.0));
```
