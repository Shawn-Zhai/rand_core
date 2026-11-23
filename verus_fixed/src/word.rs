//! The [`Word`] trait

verus! {

/// A marker trait for supported "word" types.
///
/// This is implemented for: `u32`, `u64`.
pub trait Word: sealed::Sealed {
    /// (ghost, from the developer's spec) The word whose little-endian bytes are `bytes`.
    spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self;

    /// `spec_from_le_bytes` decodes the little-endian bytes of a word (what `to_le_bytes`
    /// returns).
    proof fn lemma_spec_from_le_bytes()
        ensures
            forall|w: Self| #[trigger] Self::spec_from_le_bytes(w.spec_le_bytes()) == w,
    ;
}

/// `W::try_from(v)` for `v: usize` (the developer's spec states the index of a `BlockRng` as
/// `W::try_from_spec(i as usize) === Ok(results[0])`): the word of value `v` if `v <= W::MAX`, an
/// error otherwise. Broadcast in `block`.
pub broadcast proof fn lemma_try_from_usize_spec<W: Word>(v: usize)
    ensures
        #![trigger W::try_from_spec(v)]
        W::try_from_spec(v).is_ok() <==> v <= W::spec_max(),
        W::try_from_spec(v).is_ok() ==> W::try_from_spec(v)->Ok_0.spec_value() == v,
{
    W::lemma_try_from_usize(v, W::try_from_spec(v)->Ok_0);
}

impl Word for u32 {
    open spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self {
        vstd::bytes::spec_u32_from_le_bytes(bytes)
    }

    proof fn lemma_spec_from_le_bytes() {
        assert forall|w: u32|
            #[trigger] Self::spec_from_le_bytes(<u32 as sealed::Sealed>::spec_le_bytes(w)) == w by {
            let b = <u32 as sealed::Sealed>::spec_le_bytes(w);
            crate::trusted::axiom_spec_u32_from_le_bytes(b);
            let (b0, b1, b2, b3) = (b[0], b[1], b[2], b[3]);
            assert(((b0 as u32) | ((b1 as u32) << 8u32) | ((b2 as u32) << 16u32) | ((b3 as u32)
                << 24u32)) == w) by (bit_vector)
                requires
                    b0 == (w & 0xff) as u8,
                    b1 == ((w >> 8u32) & 0xff) as u8,
                    b2 == ((w >> 16u32) & 0xff) as u8,
                    b3 == ((w >> 24u32) & 0xff) as u8,
            ;
        }
    }
}

impl Word for u64 {
    open spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self {
        vstd::bytes::spec_u64_from_le_bytes(bytes)
    }

    proof fn lemma_spec_from_le_bytes() {
        // vstd states the `u64` encoding (`spec_u64_to_le_bytes_to_open`), so no trusted fact is
        // needed here, unlike for `u32`.
        vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
        assert forall|w: u64|
            #[trigger] Self::spec_from_le_bytes(<u64 as sealed::Sealed>::spec_le_bytes(w)) == w by {
            vstd::bytes::spec_u64_to_le_bytes_to_open(w);
            assert(<u64 as sealed::Sealed>::spec_le_bytes(w) =~= vstd::bytes::spec_u64_to_le_bytes_open(
                w,
            ));
        }
    }
}

} // verus!

use vstd::prelude::*;
// (Verus builds only: the trait of `try_from_spec`, the specification of `TryFrom::try_from`.)
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::TryFromSpec;

mod sealed {
    use vstd::prelude::*;
    // (Verus builds only: the trait of `try_from_spec`, the specification of `TryFrom::try_from`,
    // which the developer's spec uses to state the index of a `BlockRng`. Imports nothing in a
    // normal build, where the ghost code that uses it is erased.)
    #[cfg(verus_keep_ghost)]
    use vstd::std_specs::convert::TryFromSpec;

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
                vstd::layout::size_of::<Self>() == size_of::<Self>(),
                Self::spec_max() >= u32::MAX,
                forall|b: Self::Bytes| #[trigger] Self::spec_bytes(b).len() == size_of::<Self>(),
                forall|b: Self::Bytes, r: &[u8]|
                    #[trigger] <Self::Bytes as crate::trusted::std_specs::AsRefSpec<[u8]>>::as_ref_rel(&b, r)
                        ==> r@ == Self::spec_bytes(b),
                forall|w: Self| #[trigger] w.spec_le_bytes().len() == size_of::<Self>(),
                forall|w: Self| #[trigger] w.spec_value() <= Self::spec_max(),
        ;

        /// A word is determined by its value.
        proof fn lemma_value_injective(a: Self, b: Self)
            ensures
                a.spec_value() == b.spec_value() ==> a == b,
        ;

        /// `Self::try_from(v)` for `v: usize` (the developer's spec states the index of a
        /// `BlockRng` as `W::try_from_spec(i) === Ok(results[0])`): the word of value `v` if
        /// `v <= Self::MAX`, an error otherwise.
        proof fn lemma_try_from_usize(v: usize, w: Self)
            ensures
                Self::try_from_spec(v).is_ok() <==> v <= Self::spec_max(),
                Self::try_from_spec(v) === Ok(w) <==> (v <= Self::spec_max() && w.spec_value() == v),
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

        proof fn lemma_value_injective(a: Self, b: Self) {
        }

        proof fn lemma_try_from_usize(v: usize, w: Self) {
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

        proof fn lemma_value_injective(a: Self, b: Self) {
        }

        proof fn lemma_try_from_usize(v: usize, w: Self) {
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
