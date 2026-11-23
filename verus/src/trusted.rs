//! TRUSTED BASE: the parts of this crate, and of the standard library it calls, that Verus does
//! not verify.
//!
//! Every other file of the crate is verified by Verus: it has no code outside `verus!`, and no
//! `assume`, `admit`, axiom, `external_body`, `external` or `assume_specification`.
//!
//! This file has two parts.
//!
//! **Specifications of standard-library items** (S1-S6). The verified code calls these items, but
//! vstd does not specify them. Verus takes each specification on trust; each one states what the
//! standard library documents for the item, and none of them contains code.
//!
//! | id | items | specification |
//! |----|-------|---------------|
//! | S1 | trait `core::error::Error` | its supertraits (`Debug + Display`), so that `TryRng::Error` may be bounded by it |
//! | S2 | trait `core::ops::DerefMut` | `deref_mut` exists; no contract |
//! | S3 | trait `AsRef`; `<[T; N] as AsRef<[T]>>::as_ref` | `as_ref` on an array returns the array's elements as a slice |
//! | S4 | trait `AsMut`; `<[T; N] as AsMut<[T]>>::as_mut` | no contract in general; on an array, the slice is the array (writes through it are writes to the array) |
//! | S5 | `<[T]>::copy_from_slice` | requires equal lengths (otherwise it panics); `dst` becomes a copy of `src` |
//! | S6 | `u32::rotate_right` | rotation right by `n % 32` |
//!
//! **Code** (C1-C5) that Verus cannot check: upstream code, moved here unchanged except for
//! visibility, or one upstream expression or statement wrapped in a function. Each function has a
//! contract that Verus checks at every call and trusts for the body.
//!
//! | id | items | why it is not verified |
//! |----|-------|------------------------|
//! | C1 | `impl fmt::Debug for BlockRng` | formatting (`core::fmt`) is not supported by Verus. Unchanged |
//! | C2 | `panic_msg` (from `unwrap_err.rs`) | it panics with a formatted message; Verus supports neither. Its contract, `ensures false`, says that it does not return, which is what `panic!` does. Unchanged except `pub(crate)` |
//! | C3 | `check_skip`: the `assert!(n < N)` of `BlockRng::reset_and_skip` | Verus does not support panics. Its precondition is the asserted condition, so the assertion never fails in verified code; unverified callers get upstream's check, with the same message and location (`#[track_caller]`) |
//! | C4 | `check_read_words_len`: the `assert_eq!` of `utils::read_words` | as C3. Its precondition is `src.len() == N * size_of::<W>()`; that this implies upstream's condition `size_of_val(src) == size_of::<[W; N]>()` is the layout of slices and arrays (Rust Reference, "Type layout": `[T; N]` has size `N * size_of::<T>()`), which vstd does not state for arrays |
//! | C5 | `u32_to_le_bytes`, `u32_from_le_bytes`, `u64_to_le_bytes`, `u64_from_le_bytes`: the standard-library functions, called | their signatures (`[u8; size_of::<Self>()]`) cannot be given an `assume_specification`. Contract: little-endian byte order |

use crate::Infallible;
use crate::block::{BlockRng, Generator};
use core::fmt;
use vstd::prelude::*;

// ===== S1-S6: specifications of standard-library items =====

// Only in Verus builds (like vstd's own `std_specs`): a normal build has no use for
// specifications, and S2-S4 name the unstable `core::marker::PointeeSized`.
#[cfg(verus_keep_ghost)]
pub mod std_specs {
    use vstd::prelude::*;

    verus! {

    // ===== S1 =====

    #[verifier::external_trait_specification]
    pub trait ExError: core::fmt::Debug + core::fmt::Display {
        type ExternalTraitSpecificationFor: core::error::Error;
    }

    // ===== S2 =====

    #[verifier::external_trait_specification]
    pub trait ExDerefMut: core::ops::Deref + core::marker::PointeeSized {
        type ExternalTraitSpecificationFor: core::ops::DerefMut;

        fn deref_mut(&mut self) -> &mut Self::Target;
    }

    // ===== S3 =====

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
    pub trait ExAsRef<T: core::marker::PointeeSized>: core::marker::PointeeSized {
        type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

        /// `r` is the reference that `self.as_ref()` returns.
        spec fn as_ref_rel(&self, r: &T) -> bool;

        fn as_ref(&self) -> (r: &T)
            ensures
                self.as_ref_rel(r),
        ;
    }

    impl<T, const N: usize> AsRefSpecImpl<[T]> for [T; N] {
        open spec fn as_ref_rel(&self, r: &[T]) -> bool {
            r@ == self@
        }
    }

    pub assume_specification<T, const N: usize>[ <[T; N] as AsRef<[T]>>::as_ref ](a: &[T; N]) -> (r: &[T]);

    // ===== S4 =====

    #[verifier::external_trait_specification]
    pub trait ExAsMut<T: core::marker::PointeeSized>: core::marker::PointeeSized {
        type ExternalTraitSpecificationFor: core::convert::AsMut<T>;

        fn as_mut(&mut self) -> &mut T;
    }

    pub assume_specification<T, const N: usize>[ <[T; N] as AsMut<[T]>>::as_mut ](a: &mut [T; N]) -> (r: &mut [T])
        ensures
            r@ == old(a)@,
            final(a)@ == final(r)@,
    ;

    // ===== S5 =====

    pub assume_specification<T: Copy>[ <[T]>::copy_from_slice ](dst: &mut [T], src: &[T])
        requires
            old(dst)@.len() == src@.len(),
        ensures
            final(dst)@ == src@,
    ;

    // ===== S6 =====

    /// `x.rotate_right(n)`: the bits of `x` rotated right by `n % 32`.
    pub open spec fn u32_rotate_right(x: u32, n: u32) -> u32 {
        let s = n % 32;
        if s == 0 {
            x
        } else {
            (x >> s) | (x << ((32 - s) as u32))
        }
    }

    pub assume_specification[ u32::rotate_right ](x: u32, n: u32) -> (r: u32)
        ensures
            r == u32_rotate_right(x, n),
    ;

    } // verus!
}

verus! {

// ===== C2 =====

#[verifier::external_body]
pub(crate) fn panic_msg(err: impl core::error::Error) -> (r: Infallible)
    ensures
        false,
{
    panic!("rand_core::UnwrapErr: failed to unwrap: {err}")
}

// ===== C3 =====

/// `assert!(n < N)`, the check of `BlockRng::reset_and_skip`.
#[verifier::external_body]
#[track_caller]
#[inline(always)]
pub(crate) fn check_skip<const N: usize>(n: usize)
    requires
        n < N,
{
    assert!(n < N);
}

// ===== C4 =====

/// `assert_eq!(size_of_val(src), size_of::<[W; N]>())`, the check of `utils::read_words`.
#[verifier::external_body]
#[track_caller]
#[inline(always)]
pub(crate) fn check_read_words_len<W, const N: usize>(src: &[u8])
    requires
        src@.len() == N * size_of::<W>(),
{
    assert_eq!(size_of_val(src), size_of::<[W; N]>());
}

// ===== C5 =====

/// (ghost) The little-endian bytes of `x`.
pub open spec fn u32_le_bytes(x: u32) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8u32) & 0xff) as u8,
        ((x >> 16u32) & 0xff) as u8,
        ((x >> 24u32) & 0xff) as u8,
    ]
}

/// (ghost) The `u32` with little-endian bytes `b`.
pub open spec fn u32_from_le(b: Seq<u8>) -> u32 {
    (b[0] as u32) | ((b[1] as u32) << 8u32) | ((b[2] as u32) << 16u32) | ((b[3] as u32) << 24u32)
}

/// (ghost) The little-endian bytes of `x`.
pub open spec fn u64_le_bytes(x: u64) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8u64) & 0xff) as u8,
        ((x >> 16u64) & 0xff) as u8,
        ((x >> 24u64) & 0xff) as u8,
        ((x >> 32u64) & 0xff) as u8,
        ((x >> 40u64) & 0xff) as u8,
        ((x >> 48u64) & 0xff) as u8,
        ((x >> 56u64) & 0xff) as u8,
    ]
}

/// (ghost) The `u64` with little-endian bytes `b`.
pub open spec fn u64_from_le(b: Seq<u8>) -> u64 {
    (b[0] as u64) | ((b[1] as u64) << 8u64) | ((b[2] as u64) << 16u64) | ((b[3] as u64) << 24u64)
        | ((b[4] as u64) << 32u64) | ((b[5] as u64) << 40u64) | ((b[6] as u64) << 48u64)
        | ((b[7] as u64) << 56u64)
}

/// `x.to_le_bytes()`
#[verifier::external_body]
#[inline(always)]
pub(crate) fn u32_to_le_bytes(x: u32) -> (r: [u8; 4])
    ensures
        r@ == u32_le_bytes(x),
{
    x.to_le_bytes()
}

/// `u32::from_le_bytes(b)`
#[verifier::external_body]
#[inline(always)]
pub(crate) fn u32_from_le_bytes(b: [u8; 4]) -> (r: u32)
    ensures
        r == u32_from_le(b@),
{
    u32::from_le_bytes(b)
}

/// `x.to_le_bytes()`
#[verifier::external_body]
#[inline(always)]
pub(crate) fn u64_to_le_bytes(x: u64) -> (r: [u8; 8])
    ensures
        r@ == u64_le_bytes(x),
{
    x.to_le_bytes()
}

/// `u64::from_le_bytes(b)`
#[verifier::external_body]
#[inline(always)]
pub(crate) fn u64_from_le_bytes(b: [u8; 8]) -> (r: u64)
    ensures
        r == u64_from_le(b@),
{
    u64::from_le_bytes(b)
}

} // verus!

// ===== C1 =====

// Custom Debug implementation that does not expose the contents of `results`.
impl<G> fmt::Debug for BlockRng<G>
where
    G: Generator + fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BlockRng")
            .field("core", &self.core)
            .finish_non_exhaustive()
    }
}
