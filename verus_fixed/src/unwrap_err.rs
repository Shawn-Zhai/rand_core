use crate::trusted::panic_msg;
use crate::{Infallible, TryCryptoRng, TryRng};
use vstd::prelude::*;

verus! {

/// Wrapper around [`TryRng`] implementation which implements [`Rng`][crate::Rng]
/// by panicking on potential errors.
///
/// # Examples
///
/// ```rust
/// # use rand_core::{UnwrapErr, TryRng, Rng};
/// fn with_try_rng<R: TryRng>(mut rng: R) {
///     // rng does not impl Rng:
///     let _ = rng.try_next_u32(); // okay
///     // let _ = rng.next_u32(); // error
///
///     // An adapter borrowing rng:
///     let _ = UnwrapErr(&mut rng).next_u32();
///
///     // An adapter moving rng:
///     let mut rng = UnwrapErr(rng);
///     let _ = rng.next_u32();
/// }
///
/// fn call_with_unsized_try_rng<R: TryRng + ?Sized>(rng: &mut R) {
///     // R is unsized, thus we must use &mut R:
///     let mut rng = UnwrapErr(rng);
///     let _ = rng.next_u32();
/// }
/// ```
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UnwrapErr<R: TryRng>(pub R);

impl<R: TryRng> TryRng for UnwrapErr<R> {
    type Error = Infallible;

    /// (ghost) The wrapped generator returned `Ok`, and so does the wrapper (on an error it
    /// panics).
    open spec fn try_next_u32_post(pre: &Self, post: &Self, res: Result<u32, Infallible>) -> bool {
        &&& res is Ok
        &&& R::try_next_u32_post(&pre.0, &post.0, Ok(res->Ok_0))
    }

    /// (ghost) As for `try_next_u32_post`.
    open spec fn try_next_u64_post(pre: &Self, post: &Self, res: Result<u64, Infallible>) -> bool {
        &&& res is Ok
        &&& R::try_next_u64_post(&pre.0, &post.0, Ok(res->Ok_0))
    }

    /// (ghost) As for `try_next_u32_post`.
    open spec fn try_fill_bytes_post(
        pre: &Self,
        post: &Self,
        dst_pre: Seq<u8>,
        dst_post: Seq<u8>,
        res: Result<(), Infallible>,
    ) -> bool {
        &&& res is Ok
        &&& R::try_fill_bytes_post(&pre.0, &post.0, dst_pre, dst_post, Ok(()))
    }

    #[inline]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        self.0.try_next_u32().map_err(panic_msg)
    }

    #[inline]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        self.0.try_next_u64().map_err(panic_msg)
    }

    #[inline]
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        self.0.try_fill_bytes(dst).map_err(panic_msg)
    }
}

impl<R: TryCryptoRng> TryCryptoRng for UnwrapErr<R> {}

impl<'r, R: TryRng + ?Sized> UnwrapErr<&'r mut R> {
    /// Reborrow with a new lifetime
    ///
    /// Rust allows references like `&T` or `&mut T` to be "reborrowed" through
    /// coercion: essentially, the pointer is copied under a new, shorter, lifetime.
    /// Until rfcs#1403 lands, reborrows on user types require a method call.
    #[inline(always)]
    pub fn re<'b>(&'b mut self) -> (result: UnwrapErr<&'b mut R>)
    where
        'r: 'b,
        ensures
            // Human spec: the result borrows the same generator: it has the generator's current
            // state, and the state the generator is left in is the state the result leaves.
            &*result.0 === &*old(self).0,
            &*final(result.0) === &*final(self).0,
    {
        UnwrapErr(self.0)
    }
}

} // verus!
