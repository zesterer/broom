use super::Handle;

/// A tagged handle, possibly to a heap object.
///
/// [`TaggedHandle`] provides the same guarantees as [`Handle`], while enabling
/// the encoding of non-pointer data into its internal representation. This can
/// be useful for uniformly storing stack values alongside heap-allocated
/// values, both avoiding unnecessary allocations and providing better cache
/// performance.
///
/// A tagged handle can be decoded into a [`Tag`] to distinguish objects on the
/// heap from stack values.
#[derive(Debug)]
pub struct TaggedHandle<T> {
    // The tagging representation primarily relies on the following to allow us
    // to uniformly store floating-point values alongside pointers and tags:
    //
    // 1. Any floating point value with all the exponent bits set to 1 is
    //    considered NaN, but there is a distinction made between "quiet NaN"
    //    and "signalling NaN".
    // 2. On modern architectures, the upper 16 bits are unused in a pointer.
    //    These are the bits that contain the exponent and the quiet NaN bit.
    //
    // Thus we can overload the notion of quiet NaN to distinguish non-floating
    // point values. If a value would ordinarily be considered quiet NaN, we
    // consider it to be either a pointer or a simple tag depending on whether
    // or not the sign bit is set.
    //
    // The meaning of each tag is left to the application. We could potentially
    // have many more, but 8-bits are already plenty useful in practice.
    //
    // Here's a diagram showing how a floating point value is ordinarily
    // interpreted (above) as well as how we are using these bits in our
    // encoding (below).
    //
    // MSB            QNaN bit                                             LSB
    //                  |
    // sign  exponent   |                     mantissa
    //  |   ---------   | --------------------------------------------------
    //  |  /         \  |/                                                  \
    // [.][...........][Q...........................................][........]
    //  |                                                             \______/
    // pointer(y/n)?                                                    tag
    //
    // In summary:
    // - If QNaN is signalled...
    //    - and the sign bit is set: this is a pointer.
    //    - and the sign bit is unset: this is a tagged value
    // - otherwise: this is an ordinary float.
    //
    // Of course, the above condenses many details to avoid bloating this module,
    // so for further reading here are some additional references:
    //
    // https://craftinginterpreters.com/optimization.html#nan-boxing
    // https://nikic.github.io/2012/02/02/Pointer-magic-for-efficient-dynamic-value-representations.html
    // http://wingolog.org/archives/2011/05/18/value-representation-in-javascript-implementations
    handle: Handle<T>,
}

/// A decoded [`TaggedHandle`], providing access to either its internal
/// [`Handle`] or one of its tag values.
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
    /// This can be useful in situations where you would like to construct a
    /// TaggedHandle from a precomputed stack value or constant.
    ///
    /// Safety:
    ///
    /// It is only valid to create a TaggedHandle from a non-heap (tagged)
    /// value, any other value can lead to undefined behavior.
    pub unsafe fn from_raw(raw: u64) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: raw as *mut T
            },
        }
    }

    /// Return the raw (bitwise) representation of this [`TaggedHandle`].
    pub fn to_raw(&self) -> u64 {
        self.handle.ptr as u64
    }

    /// Create a [`TaggedHandle`] from a [`Handle`].
    pub fn from_handle(handle: Handle<T>) -> Self {
        let u = (handle.ptr as u64) | QNAN | SIGN;
        TaggedHandle{
            handle: Handle {
                gen: handle.gen,
                ptr: u as *mut T,
            }
        }
    }

    /// Create a [`TaggedHandle`] from a [`f64`].
    pub fn from_float(float: f64) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: f64::to_bits(float) as *mut _,
            },
        }
    }

    /// Create a [`TaggedHandle`] from a [`u8`].
    pub fn from_tag(tag: u8) -> Self {
        TaggedHandle {
            handle: Handle {
                gen: 0,
                ptr: (QNAN | (tag as u64)) as *mut _,
            },
        }
    }

    /// Decode a [`TaggedHandle`] to differentiate valid [`Handle`] objects from
    /// simple tag values.
    pub fn decode(self) -> Tag<T> {
        let u = self.handle.ptr as u64;
        if u & QNAN != QNAN {
            // Not a QNaN - ordinary float.
            return Tag::Float(f64::from_bits(u));
        }
        if (u & (QNAN | SIGN)) == (QNAN | SIGN) {
            // QNaN with a sign bit - pointer.
            let ptr = u & (!(QNAN | SIGN));
            return Tag::Handle(Handle {
                gen: self.handle.gen,
                ptr: ptr as *mut T,
            });
        }
        // All other QNaN are tag values. Mask out the lower bits.
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
        let tagged: TaggedHandle::<Value> = 2.718.into();
        assert_eq!(tagged.decode(), Tag::Float(2.718));

        let tagged: TaggedHandle::<Value> = (-3.141).into();
        assert_eq!(tagged.decode(), Tag::Float(-3.141));
    }

    #[test]
    fn tag() {
        let tag = 7;
        let tagged = TaggedHandle::<Value>::from_tag(tag);
        assert_eq!(tagged.decode(), Tag::Tag(tag));
    }
}
