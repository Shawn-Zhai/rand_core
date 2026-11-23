//! Claude's first-pass contracts, verified against the fixed crate (not part of the crate).
//!
//! The amendments weakened four preconditions (`reconstruct`, `reset_and_skip`, `word_offset`,
//! `remaining_results`) and only added postconditions. Each function below restates Claude's
//! contract from `verus/src/` verbatim and implements it by calling the fixed crate's function,
//! so its verification shows that clients written against Claude's contracts still verify.
//!
//! For the functions whose contracts only gained clauses, the restatement is immediate; they are
//! included for the functions of `block.rs` and the two strengthened trait methods.
//!
//! Verified by `verify.sh` against the crate's exported specifications.

use rand_core::block::{BlockRng, Generator};
use rand_core::utils::{self, Word};
use rand_core::{Infallible, Rng, TryRng};
use vstd::prelude::*;

verus! {

// ===== lib.rs =====

fn rng_fill_bytes<R: Rng>(rng: &mut R, dst: &mut [u8])
    ensures
        exists|res: Result<(), Infallible>|
            #[trigger] R::try_fill_bytes_post(old(rng), final(rng), old(dst)@, final(dst)@, res),
{
    rng.fill_bytes(dst)
}

fn try_fill_bytes<R: TryRng>(rng: &mut R, dst: &mut [u8]) -> (res: Result<(), R::Error>)
    ensures
        R::try_fill_bytes_post(old(rng), final(rng), old(dst)@, final(dst)@, res),
{
    rng.try_fill_bytes(dst)
}

// ===== block.rs =====

fn new<W: Word + Default, const N: usize, G: Generator<Output = [W; N]>>(core: G) -> (r: BlockRng<G>)
    requires
        0 < N <= W::spec_max(),
    ensures
        r.wf(),
        r.buffer() == Seq::<W>::empty(),
        r.spec_core() == core,
{
    BlockRng::new(core)
}

fn reconstruct<W: Word + Default, const N: usize, G: Generator<Output = [W; N]>>(
    core: G,
    remaining_results: &[W],
) -> (r: Option<BlockRng<G>>)
    requires
        0 < N <= W::spec_max(),
    ensures
        remaining_results@.len() < N ==> (r matches Some(rng) && rng.wf() && rng.buffer()
            == remaining_results@ && rng.spec_core() == core),
        remaining_results@.len() >= N ==> r is None,
{
    // (generic `W`: the developer's `W::try_from_spec(N).is_ok()` is `N <= W::spec_max()`)
    proof {
        W::lemma_try_from_usize(N, vstd::pervasive::arbitrary());
    }
    BlockRng::reconstruct(core, remaining_results)
}

fn reset_and_skip<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &mut BlockRng<G>,
    n: usize,
)
    requires
        old(rng).wf(),
        n < N,
    ensures
        final(rng).wf(),
        n == 0 ==> final(rng).buffer() == Seq::<W>::empty() && final(rng).spec_core() == old(
            rng,
        ).spec_core(),
        n > 0 ==> exists|block: [W; N]|
            #[trigger] G::generate_post(&old(rng).spec_core(), &final(rng).spec_core(), &block)
                && final(rng).buffer() == block@.subrange(n as int, N as int),
{
    // (generic `N` and `W`: `wf()` gives the developer's precondition)
    proof {
        rng.lemma_wf_human();
    }
    rng.reset_and_skip(n)
}

fn word_offset<W: Word, const N: usize, G: Generator<Output = [W; N]>>(rng: &BlockRng<G>) -> (r: usize)
    requires
        rng.wf(),
    ensures
        r == if rng.buffer().len() == 0 {
            0
        } else {
            N - rng.buffer().len()
        },
        r < N,
{
    rng.word_offset()
}

fn remaining_results<'a, W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &'a BlockRng<G>,
) -> (r: &'a [W])
    requires
        rng.wf(),
    ensures
        r@ == rng.buffer(),
        r@.len() < N,
{
    rng.remaining_results()
}

fn next_word<W: Word, const N: usize, G: Generator<Output = [W; N]>>(rng: &mut BlockRng<G>) -> (r: W)
    requires
        old(rng).wf(),
    ensures
        final(rng).wf(),
        old(rng).consumes(final(rng), 1, seq![r]),
{
    rng.next_word()
}

fn next_u64_from_u32<const N: usize, G: Generator<Output = [u32; N]>>(rng: &mut BlockRng<G>) -> (r: u64)
    requires
        old(rng).wf(),
        N >= 2,
    ensures
        final(rng).wf(),
        exists|words: Seq<u32>|
            #[trigger] old(rng).consumes(final(rng), 2, words) && r == ((words[1] as u64) << 32u64)
                | (words[0] as u64),
{
    rng.next_u64_from_u32()
}

fn fill_bytes<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    rng: &mut BlockRng<G>,
    dest: &mut [u8],
)
    requires
        old(rng).wf(),
    ensures
        final(rng).wf(),
        final(dest)@.len() == old(dest)@.len(),
        exists|k: nat, words: Seq<W>|
            {
                &&& #[trigger] old(rng).consumes(final(rng), k, words)
                &&& final(dest)@ == utils::le_bytes_of_words(words).subrange(0, old(dest)@.len() as int)
                &&& k * size_of::<W>() >= old(dest)@.len()
                &&& (k == 0 || (k - 1) * size_of::<W>() < old(dest)@.len())
            },
{
    rng.fill_bytes(dest)
}

// ===== utils.rs =====

fn read_words<W: Word, const N: usize>(src: &[u8]) -> (r: [W; N])
    requires
        src@.len() == N * size_of::<W>(),
    ensures
        utils::le_bytes_of_words(r@) == src@,
{
    utils::read_words(src)
}

fn main() {
}

} // verus!
