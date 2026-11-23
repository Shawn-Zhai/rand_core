//! The [`Generator`] trait and [`BlockRng`]
//!
//! Trait [`Generator`] may be implemented by block-generators; that is PRNGs
//! whose output is a *block* of words, such as `[u32; 16]`.
//!
//! The struct [`BlockRng`] wraps such a [`Generator`] together with an output
//! buffer and implements several methods (e.g. [`BlockRng::next_word`]) to
//! assist in the implementation of [`TryRng`]. Note that (unlike in earlier
//! versions of `rand_core`) [`BlockRng`] itself does not implement [`TryRng`]
//! since in practice we found it was always beneficial to use a wrapper type
//! over [`BlockRng`].
//!
//! # Example
//!
//! ```
//! use core::convert::Infallible;
//! use rand_core::{Rng, SeedableRng, TryRng};
//! use rand_core::block::{Generator, BlockRng};
//!
//! struct MyRngCore {
//!     // Generator state ...
//! #    state: [u32; 8],
//! }
//!
//! impl Generator for MyRngCore {
//!     type Output = [u32; 8];
//!
//!     fn generate(&mut self, output: &mut Self::Output) {
//!         // Write a new block to output...
//! #        *output = self.state;
//!     }
//! }
//!
//! // Our RNG is a wrapper over BlockRng
//! pub struct MyRng(BlockRng<MyRngCore>);
//!
//! impl SeedableRng for MyRng {
//!     type Seed = [u8; 32];
//!     fn from_seed(seed: Self::Seed) -> Self {
//!         let core = MyRngCore {
//!             // ...
//! #            state: rand_core::utils::read_words(&seed),
//!         };
//!         MyRng(BlockRng::new(core))
//!     }
//! }
//!
//! impl TryRng for MyRng {
//!     type Error = Infallible;
//!
//!     #[inline]
//!     fn try_next_u32(&mut self) -> Result<u32, Infallible> {
//!         Ok(self.0.next_word())
//!     }
//!
//!     #[inline]
//!     fn try_next_u64(&mut self) -> Result<u64, Infallible> {
//!         Ok(self.0.next_u64_from_u32())
//!     }
//!
//!     #[inline]
//!     fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Infallible> {
//!         Ok(self.0.fill_bytes(bytes))
//!     }
//! }
//!
//! // And if applicable: impl TryCryptoRng for MyRng {}
//!
//! let mut rng = MyRng::seed_from_u64(0);
//! println!("First value: {}", rng.next_u32());
//! # assert_eq!(rng.next_u32(), 1171109249);
//! ```
//!
//! [`TryRng`]: crate::TryRng
//! [`SeedableRng`]: crate::SeedableRng

use crate::utils::Word;
use vstd::prelude::*;
// (Verus builds only: the trait of `try_from_spec`, with which the developer's spec states the
// index. Imports nothing in a normal build, where the ghost code that uses it is erased.)
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::TryFromSpec;

verus! {

// The developer's spec states the index with `W::try_from_spec`; this relates it to the value of
// the stored word (a module-level `broadcast use`, so that no exec function gains a proof block).
broadcast use crate::word::lemma_try_from_usize_spec;

/// (ghost) The word `x`, the first word of a `BlockRng`'s output buffer, stores the index `i`.
/// This is the developer's `W::try_from_spec(i as usize) === Ok(x)`, by definition. The
/// developer's clauses are stated here with `index_is` so that they can be triggered on the
/// stored word `x`: triggered on `W::try_from_spec(i as usize)` (the developer's choice), a clause
/// that concludes `W::try_from_spec((i + 1) as usize) === ...` instantiates itself again, without
/// end (SPEC_REVIEW.md, H5).
pub open spec fn index_is<W: Word>(x: W, i: int) -> bool {
    W::try_from_spec(i as usize) === Ok(x)
}

/// A random (block) generator
pub trait Generator {
    /// The output type.
    ///
    /// For use with [`rand_core::block`](crate::block) code this must be `[u32; _]` or `[u64; _]`.
    type Output;

    /// (ghost) The contract of `generate`, chosen by the implementation: from state `pre`, a call
    /// may leave the generator in state `post`, with `output` written.
    spec fn generate_post(pre: &Self, post: &Self, output: &Self::Output) -> bool;

    /// Generate a new block of `output`.
    ///
    /// This must fill `output` with random data.
    fn generate(&mut self, output: &mut Self::Output)
        ensures
            Self::generate_post(old(self), final(self), final(output)),
    ;

    /// Destruct the output buffer
    ///
    /// This method is called on [`Drop`] of the [`Self::Output`] buffer.
    /// The default implementation does nothing.
    #[inline]
    fn drop(&mut self, output: &mut Self::Output)
        opens_invariants none
        no_unwind
    {
        let _ = output;
    }
}

/// RNG functionality for a block [`Generator`]
///
/// This type encompasses a [`Generator`] [`core`](Self::core) and a buffer.
/// It provides optimized implementations of methods required by an [`Rng`].
///
/// All values are consumed in-order of generation. No whole words (e.g. `u32`
/// or `u64`) are discarded, though where a word is partially used (e.g. for a
/// byte-fill whose length is not a multiple of the word size) the rest of the
/// word is discarded.
///
/// [`Rng`]: crate::Rng
#[derive(Clone)]
pub struct BlockRng<G: Generator> {
    results: G::Output,
    /// The *core* part of the RNG, implementing the `generate` function.
    pub core: G,
}

// The `fmt::Debug` implementation is in `trusted.rs`.

impl<G: Generator> Drop for BlockRng<G> {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.core.drop(&mut self.results);
    }
}

impl<W: Word + Default, const N: usize, G: Generator<Output = [W; N]>> BlockRng<G> {
    /// Create a new `BlockRng` from an existing RNG implementing
    /// `Generator`. Results will be generated on first use.
    #[inline]
    pub fn new(core: G) -> (r: BlockRng<G>)
        requires
            // (The developer's precondition, `N > 0` and `W::try_from_spec(N).is_ok()`, is the
            // same: `W::lemma_try_from_usize`.)
            0 < N <= W::spec_max(),
        ensures
            r.wf(),
            r.buffer() == Seq::<W>::empty(),
            // (also the developer's postcondition, `result.spec_core() === core`)
            r.spec_core() == core,
    {
        let mut results = [W::default(); N];
        results[0] = W::from_usize(N);
        BlockRng { core, results }
    }

    /// Reconstruct from a core and a remaining-results buffer.
    ///
    /// This may be used to deserialize using a `core` and the output of
    /// [`Self::remaining_results`].
    ///
    /// Returns `None` if `remaining_results` is too long.
    pub fn reconstruct(core: G, remaining_results: &[W]) -> (r: Option<Self>)
        requires
            // Human spec. (Upstream panics only when it builds a result: for `N == 0`, or for
            // `N > W::MAX` with `remaining_results.len() >= N`, it returns `None`.)
            remaining_results@.len() < N ==> W::try_from_spec(N).is_ok(),
        ensures
            remaining_results@.len() < N ==> (r matches Some(rng) && rng.wf() && rng.buffer()
                == remaining_results@ && rng.spec_core() == core),
            remaining_results@.len() >= N ==> r is None,
            // Human spec
            (r is None) <==> remaining_results@.len() >= N,
            match r {
                Some(rng) => rng.spec_core() === core,
                None => true,
            },
    {
        let mut results = [W::default(); N];
        if remaining_results.len() < N {
            let index = N - remaining_results.len();
            results.split_at_mut(index).1.copy_from_slice(remaining_results);
            let ghost copied = results@;
            results[0] = W::from_usize(index);
            proof {
                assert(results@.subrange(index as int, N as int) =~= copied.subrange(index as int, N as int));
                assert(copied.subrange(index as int, N as int) =~= remaining_results@);
            }
            Some(BlockRng { results, core })
        } else {
            None
        }
    }
}

impl<W: Word, const N: usize, G: Generator<Output = [W; N]>> BlockRng<G> {
    /// (ghost) The index stored in `results[0]`.
    closed spec fn spec_index(&self) -> nat {
        self.results@[0].spec_value()
    }

    /// (ghost) Well-formedness: `0 < N <= W::MAX` and the index is in `1..=N`. Every value of
    /// `BlockRng` that `new` and `reconstruct` return, and that its methods leave, is well-formed.
    pub closed spec fn wf(&self) -> bool {
        &&& 0 < N <= W::spec_max()
        &&& 1 <= self.spec_index() <= N
    }

    /// (ghost) The words of the buffer that have not been consumed yet, in order.
    pub closed spec fn buffer(&self) -> Seq<W> {
        if self.spec_index() >= N {
            Seq::empty()
        } else {
            self.results@.subrange(self.spec_index() as int, N as int)
        }
    }

    /// (ghost) The core.
    pub closed spec fn spec_core(&self) -> G {
        self.core
    }

    /// (ghost, from the developer's spec) The output buffer, whose first word holds the index.
    pub closed spec fn spec_results(&self) -> G::Output {
        self.results
    }

    /// (ghost) The words of `blocks`, in order.
    pub open spec fn blocks_words(blocks: Seq<[W; N]>) -> Seq<W>
        decreases blocks.len(),
    {
        if blocks.len() == 0 {
            Seq::empty()
        } else {
            Self::blocks_words(blocks.drop_last()) + blocks.last()@
        }
    }

    /// (ghost) Starting from the core `cores[0]`, `generate` may produce `blocks`, in order,
    /// leaving the core `cores[i + 1]` after producing `blocks[i]`.
    pub open spec fn generates(cores: Seq<G>, blocks: Seq<[W; N]>) -> bool {
        &&& cores.len() == blocks.len() + 1
        &&& forall|i: int|
            #![trigger blocks[i]]
            0 <= i < blocks.len() ==> G::generate_post(&cores[i], &cores[i + 1], &blocks[i])
    }

    /// (ghost) `next` is `self` after consuming `words`, the next `k` words of the stream: the
    /// unconsumed words of the buffer, followed by the blocks that `generate` produces. All
    /// words are consumed in order; a block is generated only once the buffer is exhausted and
    /// another word is needed, so no whole word is discarded.
    pub open spec fn consumes(&self, next: &Self, k: nat, words: Seq<W>) -> bool {
        exists|cores: Seq<G>, blocks: Seq<[W; N]>|
            {
                let stream = self.buffer() + Self::blocks_words(blocks);
                &&& #[trigger] Self::generates(cores, blocks)
                &&& cores[0] == self.spec_core()
                &&& cores.last() == next.spec_core()
                &&& k <= stream.len()
                &&& (blocks.len() > 0 ==> stream.len() - N < k)
                &&& words == stream.subrange(0, k as int)
                &&& next.buffer() == stream.subrange(k as int, stream.len() as int)
            }
    }

    /// `wf()` in the terms of the developer's spec: `N` is positive and fits in `W`, and the index
    /// stored in `results[0]` is in `1..=N`. This is the developer's precondition of `next_word`
    /// and `fill_bytes` (and, with `N >= 2`, of `next_u64_from_u32`).
    pub proof fn lemma_wf_human(&self)
        ensures
            self.wf() <==> {
                &&& N > 0
                &&& W::try_from_spec(N).is_ok()
                &&& exists|i: int|
                    1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                        self.spec_results()@[0],
                    )
            },
    {
        W::lemma_word();
        if N > 0 {
            let x = self.results@[0];
            W::lemma_try_from_usize(N, x);
            if self.wf() {
                W::lemma_try_from_usize(self.spec_index() as usize, x);
                assert(W::try_from_spec(self.spec_index() as usize) === Ok(self.spec_results()@[0]));
            }
            if exists|i: int|
                1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                    self.spec_results()@[0],
                ) {
                let i = choose|i: int|
                    1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                        self.spec_results()@[0],
                    );
                W::lemma_try_from_usize(i as usize, x);
            }
        }
    }

    /// `index_is(self.spec_results()@[0], i)`, for `i` in `0..=N`: the index is `i`.
    proof fn lemma_index_is(&self, i: int)
        requires
            0 <= i <= N,
        ensures
            index_is(self.spec_results()@[0], i) <==> (i <= W::spec_max()
                && self.spec_index() == i),
    {
        W::lemma_try_from_usize(i as usize, self.results@[0]);
    }

    /// Get the index into the result buffer.
    ///
    /// If this is equal to or larger than the size of the result buffer then
    /// the buffer is "empty" and `generate()` must be called to produce new
    /// results.
    #[inline(always)]
    fn index(&self) -> (r: usize)
        requires
            0 < N,
            self.spec_index() <= N,
        ensures
            r == self.spec_index(),
    {
        self.results[0].into_usize()
    }

    #[inline(always)]
    fn set_index(&mut self, index: usize)
        requires
            0 < index <= N,
            N <= W::spec_max(),
        ensures
            final(self).spec_index() == index,
            final(self).results@ == old(self).results@.update(0, final(self).results@[0]),
            final(self).core == old(self).core,
    {
        self.results[0] = W::from_usize(index);
    }

    /// Re-generate buffer contents, skipping the first `n` words
    ///
    /// Existing buffer contents are discarded. A new set of results is
    /// generated (either immediately or when next required). The first `n`
    /// words are skipped (this may be used to set a specific word position).
    ///
    /// # Panics
    ///
    /// This method will panic if `n >= N` where `N` is the buffer size (in
    /// words).
    #[inline]
    pub fn reset_and_skip(&mut self, n: usize)
        requires
            // Human spec (the method never reads the old index, so it needs no `old(self).wf()`)
            N > 0,
            W::try_from_spec(N).is_ok(),
            n < N,
        ensures
            final(self).wf(),
            n == 0 ==> final(self).buffer() == Seq::<W>::empty() && final(self).spec_core()
                == old(self).spec_core(),
            n > 0 ==> exists|block: [W; N]|
                #[trigger] G::generate_post(&old(self).spec_core(), &final(self).spec_core(), &block)
                    && final(self).buffer() == block@.subrange(n as int, N as int),
            // Human spec
            n == 0 ==> final(self).spec_core() === old(self).spec_core(),
            n == 0 ==> forall|i: int|
                1 <= i < N as int ==> final(self).spec_results()@[i] == old(self).spec_results()@[i],
    {
        if n == 0 {
            self.set_index(N);
            return;
        }

        crate::trusted::check_skip::<N>(n);
        self.core.generate(&mut self.results);
        let ghost block = self.results;
        self.set_index(n);
        proof {
            assert(self.buffer() =~= block@.subrange(n as int, N as int));
            assert(G::generate_post(&old(self).spec_core(), &self.spec_core(), &block));
        }
    }

    /// Get the number of words consumed since the start of the block
    ///
    /// The result is in the range `0..N` where `N` is the buffer size (in
    /// words).
    #[inline]
    pub fn word_offset(&self) -> (r: usize)
        requires
            // `wf()`, or more generally the developer's precondition of `remaining_results` (the
            // index is in `1..=N`, which `wf()` implies: `lemma_wf_human`). The developer's
            // precondition of `word_offset`, `N > 0` alone, does not suffice (SPEC_REVIEW.md, H4).
            self.wf() || (N > 0 && exists|i: int|
                1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                    self.spec_results()@[0],
                )),
        ensures
            r == if self.buffer().len() == 0 {
                0
            } else {
                N - self.buffer().len()
            },
            // (also the developer's postcondition)
            r < N,
    {
        let index = self.index();
        if index >= N { 0 } else { index }
    }

    /// Access the unused part of the results buffer
    ///
    /// The length of the returned slice is guaranteed to be less than the
    /// length of `<Self as Generator>::Output` (i.e. less than `N` where
    /// `Output = [W; N]`).
    ///
    /// This is a low-level interface intended for serialization.
    /// Results are not marked as consumed.
    #[inline]
    pub fn remaining_results(&self) -> (r: &[W])
        requires
            // `wf()`, or more generally the developer's precondition (the index is in `1..=N`,
            // without `N <= W::MAX`, which this method does not need; `wf()` implies it:
            // `lemma_wf_human`)
            self.wf() || (N > 0 && exists|i: int|
                1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                    self.spec_results()@[0],
                )),
        ensures
            r@ == self.buffer(),
            // (also the developer's postcondition)
            r@.len() < N,
    {
        let index = self.index();
        &self.results[index..N]
    }

    /// Generate the next word (e.g. `u32`)
    #[inline]
    pub fn next_word(&mut self) -> (r: W)
        requires
            // (the developer's precondition: `lemma_wf_human`)
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).consumes(final(self), 1, seq![r]),
            // Human spec
            // Case 1: the buffer is not exhausted
            forall|i: int|
                0 <= i < N as int && #[trigger] index_is(old(self).spec_results()@[0], i) ==> {
                    // return the word at the old index
                    &&& r == old(self).spec_results()@[i]
                    // core remains unchanged
                    &&& final(self).spec_core() === old(self).spec_core()
                    // the index advances by one.
                    &&& index_is(final(self).spec_results()@[0], i + 1)
                    // other buffered words remain unchanged
                    &&& forall|j: int|
                        1 <= j < N as int ==> final(self).spec_results()@[j] == old(
                            self,
                        ).spec_results()@[j]
                },
            // Case 2: the buffer is exhausted
            index_is(old(self).spec_results()@[0], N as int) ==> index_is(
                final(self).spec_results()@[0],
                1,
            ),
    {
        let ghost cores = seq![self.core];
        let ghost blocks = Seq::<[W; N]>::empty();
        let mut index = self.index();
        if index >= N {
            self.core.generate(&mut self.results);
            index = 0;
            proof {
                cores = cores.push(self.core);
                blocks = blocks.push(self.results);
            }
        }

        let value = self.results[index];
        self.set_index(index + 1);
        proof {
            lemma_blocks_words_at_most_one::<W, N, G>(blocks);
            let stream = old(self).buffer() + Self::blocks_words(blocks);
            assert(seq![value] =~= stream.subrange(0, 1));
            assert(self.buffer() =~= stream.subrange(1, stream.len() as int));
            assert(Self::generates(cores, blocks));
            assert(old(self).consumes(self, 1, seq![value]));
            // the developer's clauses: the index `i` is the old index
            assert forall|i: int|
                0 <= i < N as int && #[trigger] index_is(old(self).spec_results()@[0], i) implies {
                &&& value == old(self).spec_results()@[i]
                &&& self.spec_core() === old(self).spec_core()
                &&& index_is(self.spec_results()@[0], i + 1)
                &&& forall|j: int|
                    1 <= j < N as int ==> self.spec_results()@[j] == old(self).spec_results()@[j]
            } by {
                old(self).lemma_index_is(i);
                self.lemma_index_is(i + 1);
            }
            old(self).lemma_index_is(N as int);
            self.lemma_index_is(1);
        }
        value
    }
}

impl<const N: usize, G: Generator<Output = [u32; N]>> BlockRng<G> {
    /// Generate a `u64` from two `u32` words
    #[inline]
    pub fn next_u64_from_u32(&mut self) -> (r: u64)
        requires
            // (the developer's precondition, with `N <= u32::MAX`: `lemma_wf_human`)
            old(self).wf(),
            N >= 2,
        ensures
            final(self).wf(),
            exists|words: Seq<u32>|
                #[trigger] old(self).consumes(final(self), 2, words) && r == ((words[1] as u64)
                    << 32u64) | (words[0] as u64),
            // Human spec
            // Case 1: two words are available in the buffer
            (old(self).spec_results()@[0] as usize) < N - 1 ==> r
                == ((old(self).spec_results()@[(old(self).spec_results()@[0] as int) + 1] as u64)
                << 32) | (old(self).spec_results()@[old(self).spec_results()@[0] as int] as u64),
            // no new block is generated
            (old(self).spec_results()@[0] as usize) < N - 1 ==> forall|i: int|
                1 <= i < N as int ==> final(self).spec_results()@[i] == old(self).spec_results()@[i],
            // core remains unchanged
            (old(self).spec_results()@[0] as usize) < N - 1
                ==> final(self).spec_core() === old(self).spec_core(),
            // the buffer index is updated appropriately
            (old(self).spec_results()@[0] as usize) < N - 1
                ==> final(self).spec_results()@[0] == old(self).spec_results()@[0] + 2,
            // Case 2: one word remains
            (old(self).spec_results()@[0] as usize) == N - 1
                ==> (r & 0xFFFF_FFFFu64) == old(self).spec_results()@[N as int - 1] as u64,
            (old(self).spec_results()@[0] as usize) == N - 1
                ==> final(self).spec_results()@[0] == 1u32,
            // Case 3: buffer exhausted
            (old(self).spec_results()@[0] as usize) >= N
                ==> (r >> 32) == final(self).spec_results()@[1] as u64,
            (old(self).spec_results()@[0] as usize) >= N
                ==> final(self).spec_results()@[0] == 2u32,
    {
        let ghost cores = seq![self.core];
        let ghost blocks = Seq::<[u32; N]>::empty();
        let index = self.index();
        let mut new_index;
        let (mut lo, mut hi);
        if index < N - 1 {
            lo = self.results[index];
            hi = self.results[index + 1];
            new_index = index + 2;
        } else {
            lo = self.results[N - 1];
            self.core.generate(&mut self.results);
            proof {
                cores = cores.push(self.core);
                blocks = blocks.push(self.results);
            }
            hi = self.results[0];
            new_index = 1;
            if index >= N {
                lo = hi;
                hi = self.results[1];
                new_index = 2;
            }
        }
        self.set_index(new_index);
        proof {
            lemma_blocks_words_at_most_one::<u32, N, G>(blocks);
            let stream = old(self).buffer() + Self::blocks_words(blocks);
            assert(seq![lo, hi] =~= stream.subrange(0, 2));
            assert(self.buffer() =~= stream.subrange(2, stream.len() as int));
            assert(Self::generates(cores, blocks));
            assert(old(self).consumes(self, 2, seq![lo, hi]));
            assert(seq![lo, hi][1] == hi && seq![lo, hi][0] == lo);
            // the developer's clauses: the low and high halves of the result
            assert(((((hi as u64) << 32u64) | (lo as u64)) & 0xFFFF_FFFFu64) == lo as u64
                && ((((hi as u64) << 32u64) | (lo as u64)) >> 32u64) == hi as u64) by (bit_vector);
        }
        (u64::from(hi) << 32) | u64::from(lo)
    }
}

impl<W: Word, const N: usize, G: Generator<Output = [W; N]>> BlockRng<G> {
    /// Fill `dest`
    #[inline]
    pub fn fill_bytes(&mut self, dest: &mut [u8])
        requires
            // (the developer's precondition: `lemma_wf_human`)
            old(self).wf(),
        ensures
            final(self).wf(),
            // (also the developer's: destination length remains unchanged)
            final(dest)@.len() == old(dest)@.len(),
            // `dest` holds the little-endian bytes of the next `k` words, where `k` is the fewest
            // words that cover `dest`; the rest of the last word is discarded.
            exists|k: nat, words: Seq<W>|
                {
                    &&& #[trigger] old(self).consumes(final(self), k, words)
                    &&& final(dest)@ == crate::utils::le_bytes_of_words(words).subrange(0, old(dest)@.len() as int)
                    &&& k * size_of::<W>() >= old(dest)@.len()
                    &&& (k == 0 || (k - 1) * size_of::<W>() < old(dest)@.len())
                },
            // Human spec
            // empty destination -> entire RNG state unchanged
            old(dest)@.len() == 0 ==> *final(self) === *old(self),
            // the final buffer index is valid
            exists|i: int|
                1 <= i <= N as int && #[trigger] index_is(final(self).spec_results()@[0], i),
            // Case 1: destination fits in the remaining buffer
            forall|i: int|
                1 <= i <= N as int && #[trigger] index_is(old(self).spec_results()@[0], i)
                    && old(dest)@.len() as int <= (N as int - i) * (
                vstd::layout::size_of::<W>() as int) ==> {
                    // core remains unchanged
                    &&& final(self).spec_core() === old(self).spec_core()
                    // buffered words remain unchanged
                    &&& forall|j: int|
                        1 <= j < N as int ==> final(self).spec_results()@[j] == old(
                            self,
                        ).spec_results()@[j]
                    // index advances by the number of words consumed
                    &&& index_is(
                        final(self).spec_results()@[0],
                        i + (old(dest)@.len() as int + vstd::layout::size_of::<W>() as int - 1) / (
                        vstd::layout::size_of::<W>() as int),
                    )
                },
            // Case 2: regeneration is required
            forall|i: int|
                1 <= i <= N as int && #[trigger] index_is(old(self).spec_results()@[0], i)
                    && old(dest)@.len() as int > (N as int - i) * (
                vstd::layout::size_of::<W>() as int) ==> {
                    let size = vstd::layout::size_of::<W>() as int;
                    // bytes remaining in the old buffer
                    let remaining = (N as int - i) * size;
                    let extra = old(dest)@.len() as int - remaining;
                    // number of words consumed from regenerated blocks.
                    let words = (extra + size - 1) / size;
                    // final index, accounting for multiple regenerations
                    let new_index = ((words - 1) % N as int) + 1;
                    index_is(final(self).spec_results()@[0], new_index)
                },
    {
        let ghost len = dest@.len();
        // The words consumed so far are `stream[..consumed]`, where `stream` is the buffer
        // followed by the blocks generated so far (`inv_fill`).
        let ghost mut cores = seq![self.core];
        let ghost mut blocks = Seq::<[W; N]>::empty();
        let ghost mut stream = self.buffer();
        let ghost mut consumed: nat = 0;
        proof {
            W::lemma_word();
            self.lemma_inv_fill_init();
            assert(dest@.subrange(0, 0) =~= crate::utils::le_bytes_of_words(stream.subrange(0, 0)));
            if len == 0 {
                assert(dest@ =~= crate::utils::le_bytes_of_words(stream.subrange(0, 0)).subrange(0, 0));
            }
            assert(0 * size_of::<W>() == 0);
        }
        let mut read_len = 0;
        let mut index = self.index();
        while read_len < dest.len()
            invariant_except_break
                self.inv_fill(*old(self), cores, blocks, stream, consumed, index as int),
                read_len <= len,
                index >= 1,
                size_of::<W>() > 0,
                read_len == consumed * size_of::<W>(),
                consumed == 0 || (consumed - 1) * size_of::<W>() == read_len - size_of::<W>(),
                dest@.len() == len,
                dest@.subrange(0, read_len as int) == crate::utils::le_bytes_of_words(stream.subrange(0, consumed as int)),
                read_len == len ==> dest@ == crate::utils::le_bytes_of_words(
                    stream.subrange(0, consumed as int),
                ).subrange(0, len as int),
            ensures
                self.inv_fill(*old(self), cores, blocks, stream, consumed, index as int),
                index >= 1,
                dest@.len() == len,
                dest@ == crate::utils::le_bytes_of_words(stream.subrange(0, consumed as int)).subrange(0, len as int),
                consumed * size_of::<W>() >= len,
                consumed == 0 || (consumed - 1) * size_of::<W>() < len,
            decreases len - read_len,
        {
            proof {
                W::lemma_word();
                self.lemma_inv_fill_basic(*old(self), cores, blocks, stream, consumed, index as int);
            }
            if index >= N {
                let ghost before = *self;
                self.core.generate(&mut self.results);
                index = 0;
                proof {
                    self.lemma_inv_fill_generate(&before, *old(self), cores, blocks, stream, consumed);
                    cores = cores.push(self.core);
                    blocks = blocks.push(self.results);
                    stream = stream + self.results@;
                }
            }

            let size = core::mem::size_of::<W>();
            // `dest[read_len..].chunks_exact_mut(size)` zipped with `self.results[index..].iter()`:
            // `num_chunks` (the length of the zip) chunks `dest[read_len + i * size..][..size]`
            // and words `self.results[index + i]`. Then, if the words are not exhausted, the
            // remainder of `dest` (shorter than a word) is `dest[read_len..]`.
            let num_chunks = if (dest.len() - read_len) / size < N - index {
                (dest.len() - read_len) / size
            } else {
                N - index
            };
            proof {
                lemma_chunks(len - read_len, size as int, num_chunks as int);
                self.lemma_inv_fill_basic(*old(self), cores, blocks, stream, consumed, index as int);
            }
            let mut i = 0;
            proof {
                assert(0 * (size as int) == 0) by (nonlinear_arith);
                assert(stream.subrange(0, consumed + 0 as int) =~= stream.subrange(0, consumed as int));
            }
            while i < num_chunks
                invariant
                    dest@.len() == len,
                    i <= num_chunks,
                    size == size_of::<W>(),
                    size > 0,
                    read_len + num_chunks * size <= len,
                    index + num_chunks <= N,
                    self.inv_fill(*old(self), cores, blocks, stream, consumed, index as int),
                    dest@.subrange(0, read_len + i * size) == crate::utils::le_bytes_of_words(
                        stream.subrange(0, consumed + i),
                    ),
                decreases num_chunks - i,
            {
                proof {
                    W::lemma_word();
                    let (a, b, s) = (i as int, num_chunks as int, size as int);
                    assert((a + 1) * s <= b * s) by (nonlinear_arith)
                        requires
                            a < b,
                            s >= 0,
                    ;
                    assert((a + 1) * s == a * s + s) by (nonlinear_arith);
                    assert(dest@.len() == dest.len());
                }
                let ghost dest0 = dest@;
                let (_, chunk) = dest.split_at_mut(read_len + i * size);
                let (chunk, _) = chunk.split_at_mut(size);
                chunk.copy_from_slice(self.results[index + i].to_le_bytes().as_ref());
                proof {
                    self.lemma_inv_fill_word(*old(self), cores, blocks, stream, consumed, index as int, i as int);
                    let w = self.results@[index + i];
                    crate::utils::lemma_le_bytes_of_words_push(stream.subrange(0, consumed + i), w);
                    assert(stream.subrange(0, consumed + i + 1) =~= stream.subrange(0, consumed + i).push(w));
                    assert(dest@.subrange(0, read_len + (i + 1) * size) =~= dest0.subrange(
                        0,
                        read_len + i * size,
                    ) + crate::utils::le_bytes(w));
                }
                i += 1;
            }
            proof {
                if num_chunks > 0 {
                    self.lemma_inv_fill_advance(*old(self), cores, blocks, stream, consumed, index as int, num_chunks as int);
                }
            }
            index += num_chunks;
            read_len += num_chunks * size;
            proof {
                let (c, b, s) = (consumed as int, num_chunks as int, size as int);
                assert((c + b) * s == c * s + b * s) by (nonlinear_arith);
                assert((c + b - 1) * s == (c + b) * s - s) by (nonlinear_arith);
                consumed = (consumed + num_chunks) as nat;
            }

            if index < N {
                let src = &self.results[index];
                // We have consumed all full chunks of dest, but not src.
                let ghost dest0 = dest@;
                let (_, dest_rem) = dest.split_at_mut(read_len);
                let n = dest_rem.len();
                if n > 0 {
                    dest_rem.copy_from_slice(&src.to_le_bytes().as_ref()[0..n]);
                    proof {
                        self.lemma_inv_fill_word(*old(self), cores, blocks, stream, consumed, index as int, 0);
                        self.lemma_inv_fill_advance(*old(self), cores, blocks, stream, consumed, index as int, 1);
                    }
                    index += 1;
                    proof {
                        lemma_fill_last(
                            dest@,
                            dest0.subrange(0, read_len as int),
                            stream,
                            consumed as int,
                            n as int,
                        );
                        let (c, s) = (consumed as int, size as int);
                        assert((c + 1) * s == c * s + s) by (nonlinear_arith);
                        consumed = (consumed + 1) as nat;
                    }
                } else {
                    proof {
                        lemma_split_whole(dest0, read_len as int);
                        lemma_whole(dest0, crate::utils::le_bytes_of_words(stream.subrange(0, consumed as int)));
                        let (c, s) = (consumed as int, size as int);
                        assert(c > 0 ==> (c - 1) * s == c * s - s) by (nonlinear_arith);
                    }
                }
                break;
            }
            proof {
                if read_len == len {
                    lemma_whole(dest@, crate::utils::le_bytes_of_words(stream.subrange(0, consumed as int)));
                }
                assert(num_chunks * size >= size) by (nonlinear_arith)
                    requires
                        num_chunks >= 1,
                        size >= 0,
                ;
            }
        }
        proof {
            self.lemma_inv_fill_basic(*old(self), cores, blocks, stream, consumed, index as int);
        }
        let ghost before = *self;
        self.set_index(index);
        proof {
            self.lemma_inv_fill_end(&before, *old(self), cores, blocks, stream, consumed, index as int);
            self.lemma_fill_bytes_human(
                &before,
                *old(self),
                cores,
                blocks,
                stream,
                consumed,
                index as int,
                len as int,
            );
        }
    }

    /// (ghost) The invariant of the loop of `fill_bytes`, which consumes words of `stream`, the
    /// buffer of `start` followed by the generated `blocks`: `stream[..consumed]` are consumed,
    /// and the rest is `self.results[index..]`; until a block is generated, the output buffer is
    /// `start`'s. Opaque, to keep the loop's proof small; the lemmas below are its only users.
    #[verifier::opaque]
    closed spec fn inv_fill(
        &self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
    ) -> bool {
        &&& 0 < N <= W::spec_max()
        &&& 0 <= index <= N
        &&& Self::generates(cores, blocks)
        &&& cores[0] == start.core
        &&& cores.last() == self.core
        &&& stream == start.buffer() + Self::blocks_words(blocks)
        &&& consumed + (N - index) == stream.len()
        &&& stream.subrange(consumed as int, stream.len() as int) == self.results@.subrange(index, N as int)
        &&& (blocks.len() > 0 ==> stream.len() - N < consumed || index == 0)
        &&& (blocks.len() == 0 ==> self.results == start.results)
    }

    /// `inv_fill` holds at the start of `fill_bytes`.
    proof fn lemma_inv_fill_init(&self)
        requires
            self.wf(),
        ensures
            self.inv_fill(*self, seq![self.core], Seq::empty(), self.buffer(), 0, self.spec_index() as int),
    {
        reveal(BlockRng::inv_fill);
        lemma_blocks_words_at_most_one::<W, N, G>(Seq::empty());
        assert(self.buffer() =~= self.buffer() + Self::blocks_words(Seq::empty()));
        assert(self.buffer().subrange(0, self.buffer().len() as int) =~= self.results@.subrange(
            self.spec_index() as int,
            N as int,
        ));
    }

    /// The arithmetic facts of `inv_fill`.
    proof fn lemma_inv_fill_basic(
        &self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
    )
        requires
            self.inv_fill(start, cores, blocks, stream, consumed, index),
        ensures
            0 < N <= W::spec_max(),
            0 <= index <= N,
            consumed + (N - index) == stream.len(),
    {
        reveal(BlockRng::inv_fill);
    }

    /// The `i`-th unconsumed word of the stream is `results[index + i]`.
    proof fn lemma_inv_fill_word(
        &self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
        i: int,
    )
        requires
            self.inv_fill(start, cores, blocks, stream, consumed, index),
            0 <= i,
            index + i < N,
        ensures
            consumed + i < stream.len(),
            stream[consumed + i] == self.results@[index + i],
    {
        reveal(BlockRng::inv_fill);
        lemma_stream_word(stream, consumed, self.results@, index, i);
    }

    /// Consuming `k` more words (at least one in total from this block).
    proof fn lemma_inv_fill_advance(
        &self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
        k: int,
    )
        requires
            self.inv_fill(start, cores, blocks, stream, consumed, index),
            0 <= k,
            index + k <= N,
            index + k >= 1,
        ensures
            self.inv_fill(start, cores, blocks, stream, (consumed + k) as nat, index + k),
    {
        reveal(BlockRng::inv_fill);
        lemma_stream_skip(stream, consumed, self.results@, index, k);
    }

    /// `generate` with the buffer exhausted (`index == N`) appends a block to the stream.
    proof fn lemma_inv_fill_generate(
        &self,
        before: &Self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
    )
        requires
            before.inv_fill(start, cores, blocks, stream, consumed, N as int),
            G::generate_post(&before.core, &self.core, &self.results),
        ensures
            self.inv_fill(
                start,
                cores.push(self.core),
                blocks.push(self.results),
                stream + self.results@,
                consumed,
                0,
            ),
            (stream + self.results@).subrange(0, consumed as int) == stream.subrange(0, consumed as int),
    {
        reveal(BlockRng::inv_fill);
        lemma_inv_fill_generate(start, *self, cores, blocks, stream, consumed);
        lemma_prefix_of_append(stream, self.results@, consumed as int);
        assert(cores.push(self.core)[0] == cores[0]);
    }

    /// At the end of `fill_bytes` (after `set_index`), `start` consumed `stream[..consumed]`.
    proof fn lemma_inv_fill_end(
        &self,
        before: &Self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
    )
        requires
            before.inv_fill(start, cores, blocks, stream, consumed, index),
            1 <= index,
            self.spec_index() == index,
            self.results@ == before.results@.update(0, self.results@[0]),
            self.core == before.core,
        ensures
            self.wf(),
            start.consumes(self, consumed, stream.subrange(0, consumed as int)),
    {
        reveal(BlockRng::inv_fill);
        assert(self.buffer() =~= stream.subrange(consumed as int, stream.len() as int));
        assert(Self::generates(cores, blocks));
    }

    /// The developer's clauses of `fill_bytes(dest)` (`len == dest.len()`), from the state at the
    /// end of its loop (`before`) and after `set_index` (`self`). `consumed`, the number of words
    /// consumed, is the fewest that cover `len` bytes; `blocks`, those generated.
    proof fn lemma_fill_bytes_human(
        &self,
        before: &Self,
        start: Self,
        cores: Seq<G>,
        blocks: Seq<[W; N]>,
        stream: Seq<W>,
        consumed: nat,
        index: int,
        len: int,
    )
        requires
            before.inv_fill(start, cores, blocks, stream, consumed, index),
            start.wf(),
            1 <= index,
            self.spec_index() == index,
            self.results@ == before.results@.update(0, self.results@[0]),
            self.core == before.core,
            0 <= len,
            consumed * size_of::<W>() >= len,
            consumed == 0 || (consumed - 1) * size_of::<W>() < len,
        ensures
            len == 0 ==> *self === start,
            exists|i: int|
                1 <= i <= N as int && #[trigger] index_is(self.spec_results()@[0], i),
            forall|i: int|
                1 <= i <= N as int && #[trigger] index_is(start.spec_results()@[0], i) && len <= (
                N as int - i) * (vstd::layout::size_of::<W>() as int) ==> {
                    &&& self.spec_core() === start.spec_core()
                    &&& forall|j: int|
                        1 <= j < N as int ==> self.spec_results()@[j] == start.spec_results()@[j]
                    &&& index_is(
                        self.spec_results()@[0],
                        i + (len + vstd::layout::size_of::<W>() as int - 1) / (
                        vstd::layout::size_of::<W>() as int),
                    )
                },
            forall|i: int|
                1 <= i <= N as int && #[trigger] index_is(start.spec_results()@[0], i) && len > (
                N as int - i) * (vstd::layout::size_of::<W>() as int) ==> {
                    let size = vstd::layout::size_of::<W>() as int;
                    let remaining = (N as int - i) * size;
                    let extra = len - remaining;
                    let words = (extra + size - 1) / size;
                    let new_index = ((words - 1) % N as int) + 1;
                    index_is(self.spec_results()@[0], new_index)
                },
    {
        reveal(BlockRng::inv_fill);
        W::lemma_word();
        lemma_blocks_words_len::<W, N, G>(blocks);
        let (s, k, b, i0) = (size_of::<W>() as int, consumed as int, blocks.len() as int,
            start.spec_index() as int);
        // the stream is the `N - i0` words of the buffer, then the `b` blocks
        assert(stream.len() == (N - i0) + b * N);
        // the final index (`inv_fill`: `consumed + (N - index) == stream.len()`)
        assert(index == i0 + k - b * N);
        // the final index is in `1..=N`
        self.lemma_index_is(index);
        // `b` is 0 when the buffer covers `len`, else the fewest blocks that cover the rest
        if b > 0 {
            assert(stream.len() - N < k);
            assert(b * N - N == (b - 1) * N) by (nonlinear_arith);
            assert((b - 1) * N >= 0) by (nonlinear_arith)
                requires
                    b >= 1,
                    N >= 0,
            ;
        }
        if len == 0 {
            if k > 0 {
                assert((k - 1) * s >= 0) by (nonlinear_arith)
                    requires
                        k >= 1,
                        s > 0,
                ;
            }
            assert(b == 0);
            // `results[0]` holds the old index again
            W::lemma_value_injective(self.results@[0], start.results@[0]);
            assert(self.results =~= start.results);
        }
        assert forall|i: int|
            1 <= i <= N as int && #[trigger] index_is(start.spec_results()@[0], i) && len <= (N as int
                - i) * (vstd::layout::size_of::<W>() as int) implies {
            &&& self.spec_core() === start.spec_core()
            &&& forall|j: int|
                1 <= j < N as int ==> self.spec_results()@[j] == start.spec_results()@[j]
            &&& index_is(
                self.spec_results()@[0],
                i + (len + vstd::layout::size_of::<W>() as int - 1) / (vstd::layout::size_of::<W>() as int),
            )
        } by {
            start.lemma_index_is(i);
            // `k <= N - i0` words, all from the buffer: no block is generated
            if k > N - i0 {
                assert((k - 1) * s >= (N - i0) * s) by (nonlinear_arith)
                    requires
                        k - 1 >= N - i0,
                        s > 0,
                ;
            }
            assert(b == 0);
            lemma_ceil(len, s, k);
        }
        assert forall|i: int|
            1 <= i <= N as int && #[trigger] index_is(start.spec_results()@[0], i) && len > (N as int
                - i) * (vstd::layout::size_of::<W>() as int) implies {
            let size = vstd::layout::size_of::<W>() as int;
            let remaining = (N as int - i) * size;
            let extra = len - remaining;
            let words = (extra + size - 1) / size;
            let new_index = ((words - 1) % N as int) + 1;
            index_is(self.spec_results()@[0], new_index)
        } by {
            start.lemma_index_is(i);
            // `k > N - i0`: the buffer is used up and `w` words come from `b >= 1` blocks
            if k <= N - i0 {
                assert(k * s <= (N - i0) * s) by (nonlinear_arith)
                    requires
                        k <= N - i0,
                        s > 0,
                ;
            }
            let w = k - (N - i0);
            assert(w >= 1);
            assert(b >= 1);
            // `w` is the developer's `words`: the fewest words that cover the `extra` bytes
            assert(w * s == k * s - (N - i0) * s && (w - 1) * s == (k - 1) * s - (N - i0) * s)
                by (nonlinear_arith)
                requires
                    w == k - (N - i0),
            ;
            lemma_ceil(len - (N - i0) * s, s, w);
            // and the developer's `new_index` is the final index, `w - (b - 1) * N`
            assert((b - 1) * N == b * N - N) by (nonlinear_arith);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                w - 1,
                N as int,
                b - 1,
                w - 1 - (b - 1) * N,
            );
        }
    }
}

/// The first `c` elements of `s + t` are those of `s`.
proof fn lemma_prefix_of_append<A>(s: Seq<A>, t: Seq<A>, c: int)
    requires
        0 <= c <= s.len(),
    ensures
        (s + t).subrange(0, c) == s.subrange(0, c),
{
    assert((s + t).subrange(0, c) =~= s.subrange(0, c));
}

/// A sequence is its prefix followed by its suffix.
proof fn lemma_split_whole<A>(s: Seq<A>, p: int)
    requires
        0 <= p <= s.len(),
    ensures
        s.subrange(0, p) + s.subrange(p, s.len() as int) == s,
{
    assert(s.subrange(0, p) + s.subrange(p, s.len() as int) =~= s);
}

/// A sequence that equals its own prefix `b[..d.len()]` of a sequence `b` of the same length.
proof fn lemma_whole<A>(d: Seq<A>, b: Seq<A>)
    requires
        d.subrange(0, d.len() as int) == b,
    ensures
        d == b.subrange(0, d.len() as int),
{
    assert(d.subrange(0, d.len() as int) =~= d);
    assert(b.subrange(0, b.len() as int) =~= b);
}

/// The last, partial word of `fill_bytes`: `dest` is its prefix (the bytes of the consumed
/// words `stream[..c]`) followed by the first `n` bytes of `stream[c]`.
proof fn lemma_fill_last<W: Word>(d: Seq<u8>, prefix: Seq<u8>, stream: Seq<W>, c: int, n: int)
    requires
        0 <= c < stream.len(),
        prefix == crate::utils::le_bytes_of_words(stream.subrange(0, c)),
        0 < n <= crate::utils::le_bytes(stream[c]).len(),
        d == prefix + crate::utils::le_bytes(stream[c]).subrange(0, n),
    ensures
        d == crate::utils::le_bytes_of_words(stream.subrange(0, c + 1)).subrange(0, d.len() as int),
{
    let w = stream[c];
    assert(stream.subrange(0, c + 1) =~= stream.subrange(0, c).push(w));
    crate::utils::lemma_le_bytes_of_words_push(stream.subrange(0, c), w);
    assert(d =~= (prefix + crate::utils::le_bytes(w)).subrange(0, d.len() as int));
}

/// `generate` in `fill_bytes` (with the buffer exhausted, `index >= N`) appends a block to the
/// stream.
proof fn lemma_inv_fill_generate<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    start: BlockRng<G>,
    after: BlockRng<G>,
    cores: Seq<G>,
    blocks: Seq<[W; N]>,
    stream: Seq<W>,
    consumed: nat,
)
    requires
        stream == start.buffer() + BlockRng::<G>::blocks_words(blocks),
        BlockRng::<G>::generates(cores, blocks),
        G::generate_post(&cores.last(), &after.core, &after.results),
        consumed == stream.len(),
    ensures
        BlockRng::<G>::generates(cores.push(after.core), blocks.push(after.results)),
        stream + after.results@ == start.buffer() + BlockRng::<G>::blocks_words(
            blocks.push(after.results),
        ),
        (stream + after.results@).subrange(consumed as int, (stream + after.results@).len() as int)
            == after.results@.subrange(0, N as int),
{
    lemma_blocks_words_push::<W, N, G>(blocks, after.results);
    let (c2, b2) = (cores.push(after.core), blocks.push(after.results));
    assert forall|j: int| 0 <= j < b2.len() implies #[trigger] G::generate_post(
        &c2[j],
        &c2[j + 1],
        &b2[j],
    ) by {
        if j < blocks.len() {
            assert(c2[j] == cores[j] && c2[j + 1] == cores[j + 1] && b2[j] == blocks[j]);
        } else {
            assert(c2[j] == cores.last() && c2[j + 1] == after.core && b2[j] == after.results);
        }
    }
    assert(start.buffer() + (BlockRng::<G>::blocks_words(blocks) + after.results@) =~= stream
        + after.results@);
    assert((stream + after.results@).subrange(consumed as int, (stream + after.results@).len() as int)
        =~= after.results@.subrange(0, N as int));
}

/// The word `stream[consumed + i]` is `results[index + i]`.
proof fn lemma_stream_word<W>(stream: Seq<W>, consumed: nat, results: Seq<W>, index: int, i: int)
    requires
        0 <= index,
        index + i < results.len(),
        0 <= i,
        consumed + (results.len() - index) == stream.len(),
        stream.subrange(consumed as int, stream.len() as int) == results.subrange(
            index,
            results.len() as int,
        ),
    ensures
        stream[consumed + i] == results[index + i],
{
    let sub1 = stream.subrange(consumed as int, stream.len() as int);
    let sub2 = results.subrange(index, results.len() as int);
    assert(sub1[i] == stream[consumed + i]);
    assert(sub2[i] == results[index + i]);
}

/// After consuming `k` more words, the rest of the stream is `results[index + k..]`.
proof fn lemma_stream_skip<W>(stream: Seq<W>, consumed: nat, results: Seq<W>, index: int, k: int)
    requires
        0 <= index,
        0 <= k,
        index + k <= results.len(),
        consumed + (results.len() - index) == stream.len(),
        stream.subrange(consumed as int, stream.len() as int) == results.subrange(
            index,
            results.len() as int,
        ),
    ensures
        stream.subrange(consumed + k, stream.len() as int) == results.subrange(
            index + k,
            results.len() as int,
        ),
{
    let tail = stream.subrange(consumed as int, stream.len() as int);
    assert(stream.subrange(consumed + k, stream.len() as int) =~= tail.subrange(k, tail.len() as int));
    let rtail = results.subrange(index, results.len() as int);
    assert(results.subrange(index + k, results.len() as int) =~= rtail.subrange(k, rtail.len() as int));
}

/// `blocks_words` of no block or of one block.
proof fn lemma_blocks_words_at_most_one<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    blocks: Seq<[W; N]>,
)
    requires
        blocks.len() <= 1,
    ensures
        blocks.len() == 0 ==> BlockRng::<G>::blocks_words(blocks) == Seq::<W>::empty(),
        blocks.len() == 1 ==> BlockRng::<G>::blocks_words(blocks) == blocks[0]@,
{
    if blocks.len() == 1 {
        assert(blocks.drop_last() =~= Seq::<[W; N]>::empty());
        assert(BlockRng::<G>::blocks_words(blocks.drop_last()) =~= Seq::<W>::empty());
        assert(Seq::<W>::empty() + blocks[0]@ =~= blocks[0]@);
    }
}

/// `blocks_words` of `blocks` followed by `b`.
proof fn lemma_blocks_words_push<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    blocks: Seq<[W; N]>,
    b: [W; N],
)
    ensures
        BlockRng::<G>::blocks_words(blocks.push(b)) == BlockRng::<G>::blocks_words(blocks) + b@,
{
    assert(blocks.push(b).drop_last() =~= blocks);
}

/// `blocks_words` has `N` words per block.
proof fn lemma_blocks_words_len<W: Word, const N: usize, G: Generator<Output = [W; N]>>(
    blocks: Seq<[W; N]>,
)
    ensures
        BlockRng::<G>::blocks_words(blocks).len() == blocks.len() * N,
    decreases blocks.len(),
{
    if blocks.len() > 0 {
        lemma_blocks_words_len::<W, N, G>(blocks.drop_last());
        assert((blocks.len() - 1) * N + N == blocks.len() * N) by (nonlinear_arith);
    }
}

/// `k`, the fewest words of `s` bytes that cover `len` bytes, is the developer's
/// `(len + s - 1) / s`.
proof fn lemma_ceil(len: int, s: int, k: int)
    requires
        0 <= len,
        0 < s,
        0 <= k,
        k * s >= len,
        k == 0 || (k - 1) * s < len,
    ensures
        k == (len + s - 1) / s,
{
    let r = len + s - 1 - k * s;
    if k > 0 {
        assert((k - 1) * s == k * s - s) by (nonlinear_arith);
    } else {
        assert(k * s == 0) by (nonlinear_arith)
            requires
                k == 0,
        ;
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(len + s - 1, s, k, r);
}

/// `num_chunks`, the minimum of `rest / size` and the number of words left, covers at most
/// `rest` bytes; if it is `rest / size`, less than `size` bytes are left.
proof fn lemma_chunks(rest: int, size: int, num_chunks: int)
    requires
        0 <= rest,
        0 < size,
        0 <= num_chunks <= rest / size,
    ensures
        num_chunks * size <= rest,
        num_chunks == rest / size ==> rest - num_chunks * size < size,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rest, size);
    vstd::arithmetic::mul::lemma_mul_inequality(num_chunks, rest / size, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(rest, size);
    assert(size * (rest / size) == (rest / size) * size) by (nonlinear_arith);
}

} // verus!
