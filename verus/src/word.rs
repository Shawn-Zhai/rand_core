//! The [`Word`] trait

verus! {

/// A marker trait for supported "word" types.
///
/// This is implemented for: `u32`, `u64`.
pub trait Word: sealed::Sealed {}

impl Word for u32 {}
impl Word for u64 {}

} // verus!

// (After the first item, so that the module documentation stays with `Word` in the expanded
// code that `detect_changes.py` compares; imports are order-independent.)
use vstd::prelude::*;

mod sealed {
    use vstd::prelude::*;

    verus! {

    /// Sealed trait implemented for `u32` and `u64`.
    pub trait Sealed: Default + Copy + TryFrom<usize> + Eq + core::hash::Hash {
        type Bytes: Default + Sized + AsRef<[u8]> + AsMut<[u8]>;

        /// (ghost) The value of the word.
        spec fn spec_value(self) -> nat;

        /// (ghost) The largest value of the word type (`Self::MAX`).
        spec fn spec_max() -> nat;

        /// (ghost) The bytes of a `Bytes` array.
        spec fn spec_bytes(bytes: Self::Bytes) -> Seq<u8>;

        /// (ghost) The little-endian bytes of the word (what `to_le_bytes` returns).
        spec fn spec_le_bytes(self) -> Seq<u8>;

        /// The properties of the word type that generic code uses.
        proof fn lemma_word()
            ensures
                size_of::<Self>() == 4 || size_of::<Self>() == 8,
                Self::spec_max() >= u32::MAX,
                forall|b: Self::Bytes| #[trigger] Self::spec_bytes(b).len() == size_of::<Self>(),
                forall|b: Self::Bytes, r: &[u8]|
                    #[trigger] <Self::Bytes as crate::trusted::std_specs::AsRefSpec<[u8]>>::as_ref_rel(&b, r)
                        ==> r@ == Self::spec_bytes(b),
                forall|w: Self| #[trigger] w.spec_le_bytes().len() == size_of::<Self>(),
                forall|w: Self| #[trigger] w.spec_value() <= Self::spec_max(),
        ;

        fn from_le_bytes(bytes: Self::Bytes) -> (r: Self)
            ensures
                r.spec_le_bytes() == Self::spec_bytes(bytes),
        ;

        fn to_le_bytes(self) -> (r: Self::Bytes)
            ensures
                Self::spec_bytes(r) == self.spec_le_bytes(),
        ;

        fn from_usize(val: usize) -> (r: Self)
            requires
                val <= Self::spec_max(),
            ensures
                r.spec_value() == val,
        ;

        fn into_usize(self) -> (r: usize)
            requires
                self.spec_value() <= usize::MAX,
            ensures
                r == self.spec_value(),
        ;

        /// `bytes.as_mut()`.
        ///
        /// Generic code calls this method instead of `AsMut::as_mut` on a `Self::Bytes`:
        /// Verus cannot state a contract for `AsMut::as_mut` in general (only for arrays).
        fn bytes_as_mut(bytes: &mut Self::Bytes) -> (r: &mut [u8])
            ensures
                r@ == Self::spec_bytes(*old(bytes)),
                Self::spec_bytes(*final(bytes)) == final(r)@,
        ;
    }

    impl Sealed for u32 {
        type Bytes = [u8; 4];

        open spec fn spec_value(self) -> nat {
            self as nat
        }

        open spec fn spec_max() -> nat {
            u32::MAX as nat
        }

        open spec fn spec_bytes(bytes: [u8; 4]) -> Seq<u8> {
            bytes@
        }

        open spec fn spec_le_bytes(self) -> Seq<u8> {
            crate::trusted::u32_le_bytes(self)
        }

        proof fn lemma_word() {
        }

        #[inline(always)]
        fn from_le_bytes(bytes: Self::Bytes) -> Self {
            proof {
                crate::word::lemma_u32_le_bytes_from_le_bytes(bytes@);
            }
            crate::trusted::u32_from_le_bytes(bytes)
        }
        #[inline(always)]
        fn to_le_bytes(self) -> Self::Bytes {
            crate::trusted::u32_to_le_bytes(self)
        }

        #[inline(always)]
        fn from_usize(val: usize) -> Self {
            val.try_into().unwrap()
        }
        #[inline(always)]
        fn into_usize(self) -> usize {
            self.try_into().unwrap()
        }

        #[inline(always)]
        fn bytes_as_mut(bytes: &mut Self::Bytes) -> &mut [u8] {
            bytes.as_mut()
        }
    }

    impl Sealed for u64 {
        type Bytes = [u8; 8];

        open spec fn spec_value(self) -> nat {
            self as nat
        }

        open spec fn spec_max() -> nat {
            u64::MAX as nat
        }

        open spec fn spec_bytes(bytes: [u8; 8]) -> Seq<u8> {
            bytes@
        }

        open spec fn spec_le_bytes(self) -> Seq<u8> {
            crate::trusted::u64_le_bytes(self)
        }

        proof fn lemma_word() {
        }

        #[inline(always)]
        fn from_le_bytes(bytes: Self::Bytes) -> Self {
            proof {
                crate::word::lemma_u64_le_bytes_from_le_bytes(bytes@);
            }
            crate::trusted::u64_from_le_bytes(bytes)
        }
        #[inline(always)]
        fn to_le_bytes(self) -> Self::Bytes {
            crate::trusted::u64_to_le_bytes(self)
        }

        #[inline(always)]
        fn from_usize(val: usize) -> Self {
            val.try_into().unwrap()
        }
        #[inline(always)]
        fn into_usize(self) -> usize {
            self.try_into().unwrap()
        }

        #[inline(always)]
        fn bytes_as_mut(bytes: &mut Self::Bytes) -> &mut [u8] {
            bytes.as_mut()
        }
    }

    } // verus!
}

verus! {

/// `u32::from_le_bytes` and `u32::to_le_bytes` are inverse: the little-endian bytes of
/// `u32::from_le_bytes(b)` are `b`.
pub proof fn lemma_u32_le_bytes_from_le_bytes(b: Seq<u8>)
    requires
        b.len() == 4,
    ensures
        crate::trusted::u32_le_bytes(crate::trusted::u32_from_le(b)) == b,
{
    let (b0, b1, b2, b3) = (b[0], b[1], b[2], b[3]);
    let x = crate::trusted::u32_from_le(b);
    assert(x == (b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32));
    assert(
        ((x & 0xff) as u8 == b0 && ((x >> 8u32) & 0xff) as u8 == b1 && ((x >> 16u32) & 0xff) as u8 == b2
            && ((x >> 24u32) & 0xff) as u8 == b3)
    ) by (bit_vector)
        requires
            x == (b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32) << 24u32),
    ;
    assert(crate::trusted::u32_le_bytes(x) =~= b);
}

/// `u64::from_le_bytes` and `u64::to_le_bytes` are inverse: the little-endian bytes of
/// `u64::from_le_bytes(b)` are `b`.
pub proof fn lemma_u64_le_bytes_from_le_bytes(b: Seq<u8>)
    requires
        b.len() == 8,
    ensures
        crate::trusted::u64_le_bytes(crate::trusted::u64_from_le(b)) == b,
{
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    let x = crate::trusted::u64_from_le(b);
    assert(x == (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
        | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64));
    assert(
        ((x & 0xff) as u8 == b0 && ((x >> 8u64) & 0xff) as u8 == b1 && ((x >> 16u64) & 0xff) as u8 == b2
            && ((x >> 24u64) & 0xff) as u8 == b3 && ((x >> 32u64) & 0xff) as u8 == b4
            && ((x >> 40u64) & 0xff) as u8 == b5 && ((x >> 48u64) & 0xff) as u8 == b6
            && ((x >> 56u64) & 0xff) as u8 == b7)
    ) by (bit_vector)
        requires
            x == (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
                | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64)
                | ((b7 as u64) << 56u64),
    ;
    assert(crate::trusted::u64_le_bytes(x) =~= b);
}

} // verus!
