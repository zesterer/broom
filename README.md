# Broom

An ergonomic tracing garbage collector that supports mark 'n sweep garbage collection.

[![Cargo](https://img.shields.io/crates/v/broom.svg)](
https://crates.io/crates/broom)
[![Documentation](https://docs.rs/broom/badge.svg)](
https://docs.rs/broom)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](
https://github.com/zesterer/broom)

## Features

- Ergonomic API
- Mark and sweep heap cleaning
- Easy (and safe) mutation of heap values, despite cycles
- Zero-cost access to heap objects through handles

## Example

```rust
use broom::{Handle, Trace, Tracer, Heap};

// The type you want the heap to contain
pub enum Object {
    Num(f64),
    List(Vec<Handle<Self>>),
}

// Tell the garbage collector how to explore a graph of this object
impl Trace<Self> for Object {
    fn trace(&self, tracer: &mut Tracer<Self>) {
        match self {
            Object::Num(_) => {},
            Object::List(objects) => objects.trace(tracer),
        }
    }
}

// Create a new heap
let mut heap = Heap::default();

// Temporary objects are cheaper than rooted objects, but don't survive heap cleans
let a = heap.insert_temp(Object::Num(42.0));
let b = heap.insert_temp(Object::Num(1337.0));

// Turn the numbers into a rooted list
let c = heap.insert(Object::List(vec![a, b]));

// Change one of the numbers - this is safe, even if the object is self-referential!
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
- People that want to have complex graph data structure with mutation and cycles and don't want memory leaks

## Who this crate is not for

- People that want garbage collection when writing ordinary Rust code

## TODO

There are a few things I want to do with `broom` if I get the time:

- Smarter cleanup strategies than mark 'n sweep
- Partial cleans to prevent garbage collection lag spikes

If you're interested in working on any of these things, feel free to open a pull request!
