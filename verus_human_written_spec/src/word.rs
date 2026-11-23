//! The [`Word`] trait

use vstd::prelude::*;

verus! {

/// A marker trait for supported "word" types.
///
/// This is implemented for: `u32`, `u64`.
pub trait Word: sealed::Sealed {
    spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self;
}

impl Word for u32 {
    open spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self {
        vstd::bytes::spec_u32_from_le_bytes(bytes)
    }
}

impl Word for u64 {
    open spec fn spec_from_le_bytes(bytes: Seq<u8>) -> Self {
        vstd::bytes::spec_u64_from_le_bytes(bytes)
    }
}

mod sealed {
    /// Sealed trait implemented for `u32` and `u64`.
    pub trait Sealed: Default + Copy + TryFrom<usize> + Eq + core::hash::Hash {
        type Bytes: Default + Sized + AsRef<[u8]> + AsMut<[u8]>;

        fn from_le_bytes(bytes: Self::Bytes) -> Self;
        fn to_le_bytes(self) -> Self::Bytes;

        fn from_usize(val: usize) -> Self;
        fn into_usize(self) -> usize;
    }

    impl Sealed for u32 {
        type Bytes = [u8; 4];

        #[inline(always)]
        #[verifier::external_body]
        fn from_le_bytes(bytes: Self::Bytes) -> Self {
            Self::from_le_bytes(bytes)
        }
        #[inline(always)]
        #[verifier::external_body]
        fn to_le_bytes(self) -> Self::Bytes {
            Self::to_le_bytes(self)
        }

        #[inline(always)]
        fn from_usize(val: usize) -> Self {
            assume(false);
            val.try_into().unwrap()
        }
        #[inline(always)]
        fn into_usize(self) -> usize {
            assume(false);
            self.try_into().unwrap()
        }
    }

    impl Sealed for u64 {
        type Bytes = [u8; 8];

        #[inline(always)]
        #[verifier::external_body]
        fn from_le_bytes(bytes: Self::Bytes) -> Self {
            Self::from_le_bytes(bytes)
        }
        #[inline(always)]
        #[verifier::external_body]
        fn to_le_bytes(self) -> Self::Bytes {
            Self::to_le_bytes(self)
        }

        #[inline(always)]
        fn from_usize(val: usize) -> Self {
            assume(false);
            val.try_into().unwrap()
        }
        #[inline(always)]
        fn into_usize(self) -> usize {
            assume(false);
            self.try_into().unwrap()
        }
    }
}

}