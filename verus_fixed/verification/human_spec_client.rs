//! The developer's contracts, verified against the fixed crate (not part of the crate).
//!
//! Each function below restates a contract of the developer's spec
//! (`verus_human_written_spec/src/`) and implements it by calling the fixed crate's function.
//! The `requires` and `ensures` clauses are the developer's, verbatim, including their triggers.
//! That a wrapper verifies shows that the fixed contract refines the developer's: the
//! developer's precondition implies the fixed one, and the fixed postcondition implies the
//! developer's. The developer's contracts that are only `ensures true` are left out.
//!
//! Three wrappers need one more precondition than the developer's, marked `EXTRA`: there the
//! developer's precondition does not suffice (SPEC_REVIEW.md, H2, H3 and H4).
//!
//! Verified by `verify.sh` against the crate's exported specifications, like
//! `client_examples.rs`.

use rand_core::block::{BlockRng, Generator, index_is};
use rand_core::utils::{self, Word};
use rand_core::{Rng, TryRng, UnwrapErr};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::TryFromSpec;

verus! {

// ===== lib.rs =====

fn rng_fill_bytes<R: Rng>(rng: &mut R, dst: &mut [u8])
    ensures
        final(dst)@.len() == old(dst)@.len(),
{
    rng.fill_bytes(dst)
}

fn try_fill_bytes<R: TryRng>(rng: &mut R, dst: &mut [u8]) -> (result: Result<(), R::Error>)
    ensures
        final(dst)@.len() == old(dst)@.len(),
{
    rng.try_fill_bytes(dst)
}

// ===== block.rs =====

/// `N` fits in `W` (the developer's `W::try_from_spec(N).is_ok()`).
proof fn lemma_fits<W: Word>(n: usize)
    ensures
        W::try_from_spec(n).is_ok() <==> n <= W::spec_max(),
{
    W::lemma_try_from_usize(n, vstd::pervasive::arbitrary());
}

fn new<W: Word + Default, const N: usize, G: Generator<Output = [W; N]>>(core: G) -> (result:
    BlockRng<G>)
    requires
        N > 0,
        W::try_from_spec(N).is_ok(),
    ensures
        result.spec_core() === core,
{
    proof {
        lemma_fits::<W>(N);
    }
    BlockRng::new(core)
}

fn reconstruct<W: Word + Default, const N: usize, G: Generator<Output = [W; N]>>(
    core: G,
    remaining_results: &[W],
) -> (result: Option<BlockRng<G>>)
    requires
        remaining_results@.len() < N ==> W::try_from_spec(N).is_ok(),
    ensures
        (result is None) <==> remaining_results@.len() >= N,
        match result {
            Some(r) => r.spec_core() === core,
            None => true,
        },
{
    BlockRng::reconstruct(core, remaining_results)
}

fn reset_and_skip<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &mut BlockRng<G>,
    n: usize,
)
    requires
        N > 0,
        W::try_from_spec(N).is_ok(),
        n < N,
    ensures
        n == 0 ==> final(rng).spec_core() === old(rng).spec_core(),
        n == 0 ==> forall|i: int|
            1 <= i < N as int ==> final(rng).spec_results()@[i] == old(rng).spec_results()@[i],
{
    rng.reset_and_skip(n)
}

fn word_offset<W: Word, const N: usize, G: Generator<Output = [W; N]>>(rng: &BlockRng<G>) -> (result:
    usize)
    requires
        N > 0,
        // EXTRA (H4): the index is in `1..=N`, as for `remaining_results`
        exists|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                rng.spec_results()@[0],
            ),
    ensures
        result < N,
{
    proof {
        let i = choose|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                rng.spec_results()@[0],
            );
        assert(index_is(rng.spec_results()@[0], i));
    }
    rng.word_offset()
}

fn remaining_results<'a, W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &'a BlockRng<G>,
) -> (result: &'a [W])
    requires
        N > 0,
        exists|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                rng.spec_results()@[0],
            ),
    ensures
        result@.len() < N,
{
    proof {
        let i = choose|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                rng.spec_results()@[0],
            );
        assert(index_is(rng.spec_results()@[0], i));
    }
    rng.remaining_results()
}

fn next_word<W: Word, const N: usize, G: Generator<Output = [W; N]>>(rng: &mut BlockRng<G>) -> (result: W)
    requires
        N > 0,
        W::try_from_spec(N).is_ok(),
        exists|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ),
    ensures
        // Case 1: the buffer is not exhausted
        forall|i: int|
            0 <= i < N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ) ==> {
                // return the word at the old index
                &&& result == old(rng).spec_results()@[i]
                // core remains unchanged
                &&& final(rng).spec_core() === old(rng).spec_core()
                // the index advances by one.
                &&& W::try_from_spec((i + 1) as usize) === Ok(final(rng).spec_results()@[0])
                // other buffered words remain unchanged
                &&& forall|j: int|
                    1 <= j < N as int ==> final(rng).spec_results()@[j] == old(
                        rng,
                    ).spec_results()@[j]
            },
        // Case 2: the buffer is exhausted
        W::try_from_spec(N) === Ok(old(rng).spec_results()@[0]) ==> W::try_from_spec(1usize)
            === Ok(final(rng).spec_results()@[0]),
{
    proof {
        rng.lemma_wf_human();
    }
    let ghost old_rng = *rng;
    let result = rng.next_word();
    proof {
        assert forall|i: int|
            0 <= i < N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old_rng.spec_results()@[0],
            ) implies {
            &&& result == old_rng.spec_results()@[i]
            &&& rng.spec_core() === old_rng.spec_core()
            &&& W::try_from_spec((i + 1) as usize) === Ok(rng.spec_results()@[0])
            &&& forall|j: int|
                1 <= j < N as int ==> rng.spec_results()@[j] == old_rng.spec_results()@[j]
        } by {
            assert(index_is(old_rng.spec_results()@[0], i));
        }
        assert(index_is(old_rng.spec_results()@[0], N as int) ==> index_is(
            rng.spec_results()@[0],
            1,
        ));
    }
    result
}

fn next_u64_from_u32<const N: usize, G: Generator<Output = [u32; N]>>(rng: &mut BlockRng<G>) -> (result: u64)
    requires
        N >= 2,
        N <= u32::MAX as usize,
        exists|i: int|
            1 <= i <= N as int && #[trigger] u32::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ),
    ensures
        // Case 1: two words are available in the buffer
        (old(rng).spec_results()@[0] as usize) < N - 1 ==> result == ((old(
            rng,
        ).spec_results()@[(old(rng).spec_results()@[0] as int) + 1] as u64) << 32) | (old(
            rng,
        ).spec_results()@[old(rng).spec_results()@[0] as int] as u64),
        // no new block is generated
        (old(rng).spec_results()@[0] as usize) < N - 1 ==> forall|i: int|
            1 <= i < N as int ==> final(rng).spec_results()@[i] == old(rng).spec_results()@[i],
        // core remains unchanged
        (old(rng).spec_results()@[0] as usize) < N - 1 ==> final(rng).spec_core() === old(
            rng,
        ).spec_core(),
        // the buffer index is updated appropriately
        (old(rng).spec_results()@[0] as usize) < N - 1 ==> final(rng).spec_results()@[0] == old(
            rng,
        ).spec_results()@[0] + 2,
        // Case 2: one word remains
        (old(rng).spec_results()@[0] as usize) == N - 1 ==> (result & 0xFFFF_FFFFu64) == old(
            rng,
        ).spec_results()@[N as int - 1] as u64,
        (old(rng).spec_results()@[0] as usize) == N - 1 ==> final(rng).spec_results()@[0] == 1u32,
        // Case 3: buffer exhausted
        (old(rng).spec_results()@[0] as usize) >= N ==> (result >> 32) == final(rng).spec_results()@[1] as u64,
        (old(rng).spec_results()@[0] as usize) >= N ==> final(rng).spec_results()@[0] == 2u32,
{
    proof {
        rng.lemma_wf_human();
    }
    rng.next_u64_from_u32()
}

fn fill_bytes<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &mut BlockRng<G>,
    dest: &mut [u8],
)
    requires
        N > 0,
        W::try_from_spec(N).is_ok(),
        exists|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ),
    ensures
        // destination length remains unchanged
        final(dest)@.len() == old(dest)@.len(),
        // empty destination -> entire RNG state unchanged
        old(dest)@.len() == 0 ==> *final(rng) === *old(rng),
        // the final buffer index is valid
        exists|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                final(rng).spec_results()@[0],
            ),
        // Case 1: destination fits in the remaining buffer
        forall|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ) && old(dest)@.len() as int <= (N as int - i) * (vstd::layout::size_of::<W>() as int)
                ==> {
                // core remains unchanged
                &&& final(rng).spec_core() === old(rng).spec_core()
                // buffered words remain unchanged
                &&& forall|j: int|
                    1 <= j < N as int ==> final(rng).spec_results()@[j] == old(
                        rng,
                    ).spec_results()@[j]
                // index advances by the number of words consumed
                &&& W::try_from_spec(
                    (i + (old(dest)@.len() as int + vstd::layout::size_of::<W>() as int - 1) / (
                    vstd::layout::size_of::<W>() as int)) as usize,
                ) === Ok(final(rng).spec_results()@[0])
            },
        // Case 2: regeneration is required
        forall|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old(rng).spec_results()@[0],
            ) && old(dest)@.len() as int > (N as int - i) * (vstd::layout::size_of::<W>() as int)
                ==> {
                let size = vstd::layout::size_of::<W>() as int;
                // bytes remaining in the old buffer
                let remaining = (N as int - i) * size;
                let extra = old(dest)@.len() as int - remaining;
                // number of words consumed from regenerated blocks.
                let words = (extra + size - 1) / size;
                // final index, accounting for multiple regenerations
                let new_index = ((words - 1) % N as int) + 1;
                W::try_from_spec(new_index as usize) === Ok(final(rng).spec_results()@[0])
            },
{
    proof {
        rng.lemma_wf_human();
    }
    let ghost old_rng = *rng;
    let ghost len = dest@.len() as int;
    rng.fill_bytes(dest);
    proof {
        let s = vstd::layout::size_of::<W>() as int;
        let i = choose|i: int| 1 <= i <= N as int && #[trigger] index_is(rng.spec_results()@[0], i);
        assert(W::try_from_spec(i as usize) === Ok(rng.spec_results()@[0]));
        assert forall|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old_rng.spec_results()@[0],
            ) && len <= (N as int - i) * s implies {
            &&& rng.spec_core() === old_rng.spec_core()
            &&& forall|j: int|
                1 <= j < N as int ==> rng.spec_results()@[j] == old_rng.spec_results()@[j]
            &&& W::try_from_spec((i + (len + s - 1) / s) as usize) === Ok(rng.spec_results()@[0])
        } by {
            assert(index_is(old_rng.spec_results()@[0], i));
        }
        assert forall|i: int|
            1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                old_rng.spec_results()@[0],
            ) && len > (N as int - i) * s implies {
            let words = ((len - (N as int - i) * s) + s - 1) / s;
            W::try_from_spec((((words - 1) % N as int) + 1) as usize) === Ok(
                rng.spec_results()@[0],
            )
        } by {
            assert(index_is(old_rng.spec_results()@[0], i));
        }
    }
}

// ===== utils.rs =====

fn fill_bytes_via_next_word<E, W: Word>(
    dst: &mut [u8],
    next_word: impl FnMut() -> Result<W, E>,
) -> (result: Result<(), E>)
    requires
        // EXTRA (H3): `next_word` may be called
        forall|| next_word.requires(()),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        old(dst)@.len() == 0 ==> result.is_ok(),
        old(dst)@.len() == 0 ==> final(dst)@ === old(dst)@,
{
    utils::fill_bytes_via_next_word(dst, next_word)
}

fn read_words<W: Word, const N: usize>(src: &[u8]) -> (result: [W; N])
    requires
        src@.len() == vstd::layout::size_of::<[W; N]>(),
        // EXTRA (H2): vstd does not state the size of an array, so the developer's precondition
        // says nothing about the length of `src`
        src@.len() == N * size_of::<W>(),
    ensures
        result@.len() == N,
        // each word is decoded from its corresponding input bytes in little-endian order
        forall|i: int|
            0 <= i < N as int ==> result@[i] == W::spec_from_le_bytes(
                src@.subrange(
                    i * vstd::layout::size_of::<W>() as int,
                    (i + 1) * vstd::layout::size_of::<W>() as int,
                ),
            ),
{
    utils::read_words(src)
}

// ===== unwrap_err.rs =====

fn re<'r, 'b, R: TryRng + ?Sized>(u: &'b mut UnwrapErr<&'r mut R>) -> (result: UnwrapErr<&'b mut R>)
    ensures
        &*result.0 === &*old(u).0,
        &*final(result.0) === &*final(u).0,
{
    u.re()
}

fn main() {
}

} // verus!
