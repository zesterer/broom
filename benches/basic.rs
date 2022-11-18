#![feature(test)]

extern crate test;

use broom::prelude::*;
use rand::prelude::*;
use test::{black_box, Bencher};

pub enum Value {
    Root,
    Two(Handle<Value>, Handle<Value>),
}

impl Trace<Self> for Value {
    fn trace(&self, tracer: &mut Tracer<Self>) {
        if let Value::Two(a, b) = self {
            a.trace(tracer);
            b.trace(tracer);
        }
    }
}

fn make_complex_heap() -> (Heap<Value>, Handle<Value>) {
    let mut heap = Heap::default();

    let mut root = heap.insert_temp(Value::Root);
    let mut items = Vec::new();
    for _ in 1..10000 {
        items.push(root);
        let a = items.choose(&mut thread_rng()).unwrap();
        root = heap.insert_temp(Value::Two(*a, root));
    }

    (heap, root)
}

#[bench]
fn insert(b: &mut Bencher) {
    let mut heap = Heap::default();

    b.iter(|| heap.insert(Value::Root));
}

#[bench]
fn insert_temp(b: &mut Bencher) {
    let mut heap = Heap::default();

    b.iter(|| heap.insert_temp(Value::Root));
}

#[bench]
fn fill_basic(b: &mut Bencher) {
    b.iter(|| {
        let mut heap = Heap::default();
        for _ in 0..10000 {
            heap.insert_temp(Value::Root);
        }
        black_box(heap)
    });
}

#[bench]
fn fill_complex(b: &mut Bencher) {
    b.iter(|| black_box(make_complex_heap()));
}

#[bench]
fn fill_and_clean(b: &mut Bencher) {
    b.iter(|| {
        let (mut heap, _) = make_complex_heap();
        heap.clean();
        assert_eq!(heap.len(), 0);
    });
}

#[bench]
fn fill_and_try_clean(b: &mut Bencher) {
    b.iter(|| {
        let (mut heap, root) = make_complex_heap();
        let len = heap.len();
        heap.clean_excluding(Some(root));
        assert_eq!(heap.len(), len);
    });
}
