use super::Handle;

/// A tagged handle, possibly to a heap object.
///
/// [`TaggedHandle`] provides the same guarantees as [`Handle`], while enabling the encoding of non-pointer
/// data into its internal representation.
///
/// A tagged handle can be decoded into a [`Tag`] to distinguish objects on the heap from stack values.
#[derive(Debug)]
pub struct TaggedHandle<T> {
    handle: Handle<T>,
}

/// A decoded [`TaggedHandle`], providing access to either its internal [`Handle`] or one of its
/// tag values.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Tag<T> {
    Tag(u8),
    Float(f64),
    Handle(Handle<T>),
}

const QNAN: u64 = 0x7ffc000000000000;
const SIGN: u64 = 1 << 63;

impl<T> TaggedHandle<T> {
    /// Create a [`TaggedHandle`] given a raw representation of its pointer.
    ///
    /// Safety:
    ///
    /// It is only valid to create a TaggedHandle from a non-heap (tagged) value.
    pub unsafe fn from_raw(raw: u64) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: raw as *mut T
            },
        }
    }

    /// Return the raw representation of this [`TaggedHandle`]'s pointer.
    pub fn to_raw(&self) -> u64 {
        self.handle.ptr as u64
    }

    /// Create a [`TaggedHandle`] that contains a [`Handle`].
    pub fn from_handle(handle: Handle<T>) -> Self {
        let u = (handle.ptr as u64) | QNAN | SIGN;
        TaggedHandle{
            handle: Handle {
                gen: handle.gen,
                ptr: u as *mut T,
            }
        }
    }

    /// Create a [`TaggedHandle`] that contains a [`f64`].
    pub fn from_float(float: f64) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: unsafe { ::std::mem::transmute(float) },
            },
        }
    }

    /// Create a [`TaggedHandle`] that contains a [`u8`].
    pub fn from_tag(tag: u8) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: unsafe { ::std::mem::transmute(QNAN | (tag as u64)) },
            },
        }
    }

    /// Decode a [`TaggedHandle`] to differentiate valid [`Handle`] objects from simple tag values.
    pub fn decode(self) -> Tag<T> {
        let u = self.handle.ptr as u64;
        if u & QNAN != QNAN {
            return Tag::Float(unsafe { ::std::mem::transmute(u) });
        }
        // sign bit indicates pointer
        if (u & (QNAN | SIGN)) == (QNAN | SIGN) {
            // FIXME
            let ptr = u & (!(QNAN | SIGN)); // only keep lower 51 bits
            return Tag::Handle(Handle {
                gen: self.handle.gen,
                ptr: ptr as *mut T,
            });
        }
        let tag: u8 = (u & 7) as u8;
        Tag::Tag(tag)
    }
}

impl<T> Clone for TaggedHandle<T> {
    fn clone(&self) -> Self {
        TaggedHandle { handle: self.handle }
    }
}
impl<T> Copy for TaggedHandle<T> {}

impl<T> PartialEq<Self> for TaggedHandle<T> {
    fn eq(&self, other: &Self) -> bool {
        self.handle == other.handle
    }
}
impl<T> Eq for TaggedHandle<T> {}

impl<T> From<Handle<T>> for TaggedHandle<T> {
    fn from(handle: Handle<T>) -> Self {
        Self::from_handle(handle)
    }
}

impl<T> From<f64> for TaggedHandle<T> {
    fn from(float: f64) -> Self {
        Self::from_float(float)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use super::*;

    #[derive(Debug, PartialEq)]
    struct Value;

    impl<'a> Trace<Self> for Value {
        fn trace(&self, _tracer: &mut Tracer<Self>) {}
    }

    #[test]
    fn handle() {
        let mut heap = Heap::default();
        let a = heap.insert(Value);
        let tagged: TaggedHandle<_> = a.handle().into();

        heap.clean();

        match tagged.decode() {
            Tag::Tag(_) => panic!("Expected a Tag::Handle, got Tag::Tag."),
            Tag::Float(_) => panic!("Expected a Tag::Handle, got Tag::Float."),
            Tag::Handle(h) => assert_eq!(heap.contains(&h), true, "Decoded handle is invalid."),
        }
    }

    #[test]
    fn float() {
        let tagged: TaggedHandle::<Value> = 42.314.into();
        assert_eq!(tagged.decode(), Tag::Float(42.314));
    }

    #[test]
    fn tag() {
        let tag = 7;
        let tagged = TaggedHandle::<Value>::from_tag(tag);
        assert_eq!(tagged.decode(), Tag::Tag(tag));
    }
}
