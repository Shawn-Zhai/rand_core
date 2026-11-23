//! Utilties to aid trait implementations
//!
//! ## Portability
//!
//! For cross-platform reproducibility, Little-Endian order (least-significant
//! part first) has been chosen as the standard for inter-type conversion.
//! For example, [`next_u64_via_u32`] generates two `u32` values `x, y`,
//! then outputs `(y << 32) | x`.
//!
//! Byte-swapping (like the std `to_le` functions) is only needed to convert
//! to/from byte sequences, and since its purpose is reproducibility,
//! non-reproducible sources (e.g. `OsRng`) need not bother with it.
//!
//! ## Implementing [`TryRng`]
//!
//! Usually an implementation of [`TryRng`] will implement one of the three
//! methods over its internal source. The following helpers are provided for
//! the remaining implementations.
//!
//! **`fn try_next_u32`:**
//! -   `self.next_u64() as u32`
//! -   `(self.next_u64() >> 32) as u32`
//! -   <code>[next_word_via_fill][](self)</code>
//!
//! **`fn try_next_u64`:**
//! -   <code>[next_u64_via_u32][](self)</code>
//! -   <code>[next_word_via_fill][](self)</code>
//!
//! **`fn try_fill_bytes`:**
//! -   <code>[fill_bytes_via_next_word][](self, dest)</code>
//!
//! ## Implementing [`SeedableRng`]
//!
//! In many cases, [`SeedableRng::Seed`] must be converted to `[u32; _]` or
//! `[u64; _]`. [`read_words`] may be used for this.
//!
//! [`SeedableRng`]: crate::SeedableRng
//! [`SeedableRng::Seed`]: crate::SeedableRng::Seed
//!
//! ## Example
//!
//! We demonstrate a simple multiplicative congruential generator (MCG), taken
//! from M.E. O'Neill's blog post [Does It Beat the Minimal Standard?][0].
//!
//! [0]: https://www.pcg-random.org/posts/does-it-beat-the-minimal-standard.html
//!
//! ```
//! use core::convert::Infallible;
//! use rand_core::{Rng, SeedableRng, TryRng, utils};
//!
//! pub struct Mcg128(u128);
//!
//! impl SeedableRng for Mcg128 {
//!     type Seed = [u8; 16];
//!
//!     #[inline]
//!     fn from_seed(seed: Self::Seed) -> Self {
//!         // Always use little-endian byte order to ensure portable results
//!         Self(u128::from_le_bytes(seed))
//!     }
//! }
//!
//! impl TryRng for Mcg128 {
//!     type Error = Infallible;
//!
//!     #[inline]
//!     fn try_next_u32(&mut self) -> Result<u32, Infallible> {
//!         Ok((self.next_u64() >> 32) as u32)
//!     }
//!
//!     #[inline]
//!     fn try_next_u64(&mut self) -> Result<u64, Infallible> {
//!         self.0 = self.0.wrapping_mul(0x0fc94e3bf4e9ab32866458cd56f5e605);
//!         Ok((self.0 >> 64) as u64)
//!     }
//!
//!     #[inline]
//!     fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
//!         utils::fill_bytes_via_next_word(dst, || self.try_next_u64())
//!     }
//! }
//! #
//! # let mut rng = Mcg128::seed_from_u64(42);
//! # assert_eq!(rng.next_u32(), 3443086493);
//! # assert_eq!(rng.next_u64(), 3462997187007721903);
//! # let mut buf = [0u8; 5];
//! # rng.fill_bytes(&mut buf);
//! # assert_eq!(buf, [154, 23, 43, 68, 75]);
//! ```

use crate::TryRng;
pub use crate::word::Word;
use vstd::prelude::*;

verus! {

/// (ghost) The little-endian bytes of the word `w`: what `w.to_le_bytes()` returns.
pub open spec fn le_bytes<W: Word>(w: W) -> Seq<u8> {
    w.spec_le_bytes()
}

/// The little-endian bytes of a `u32`.
pub proof fn lemma_le_bytes_u32(x: u32)
    ensures
        le_bytes(x) == seq![
            (x & 0xff) as u8,
            ((x >> 8u32) & 0xff) as u8,
            ((x >> 16u32) & 0xff) as u8,
            ((x >> 24u32) & 0xff) as u8,
        ],
{
}

/// The little-endian bytes of a `u64`.
pub proof fn lemma_le_bytes_u64(x: u64)
    ensures
        le_bytes(x) == seq![
            (x & 0xff) as u8,
            ((x >> 8u64) & 0xff) as u8,
            ((x >> 16u64) & 0xff) as u8,
            ((x >> 24u64) & 0xff) as u8,
            ((x >> 32u64) & 0xff) as u8,
            ((x >> 40u64) & 0xff) as u8,
            ((x >> 48u64) & 0xff) as u8,
            ((x >> 56u64) & 0xff) as u8,
        ],
{
}

/// (ghost) The little-endian bytes of `words`, in order.
pub open spec fn le_bytes_of_words<W: Word>(words: Seq<W>) -> Seq<u8>
    decreases words.len(),
{
    if words.len() == 0 {
        Seq::empty()
    } else {
        le_bytes_of_words(words.drop_last()) + le_bytes(words.last())
    }
}

/// `le_bytes_of_words` has `size_of::<W>()` bytes per word.
pub proof fn lemma_le_bytes_of_words_len<W: Word>(words: Seq<W>)
    ensures
        le_bytes_of_words(words).len() == words.len() * size_of::<W>(),
    decreases words.len(),
{
    W::lemma_word();
    if words.len() > 0 {
        lemma_le_bytes_of_words_len(words.drop_last());
        let n = words.len() as int;
        let s = size_of::<W>() as int;
        assert((n - 1) * s + s == n * s) by (nonlinear_arith);
    }
}

/// `le_bytes_of_words` of `words` followed by `w`.
pub proof fn lemma_le_bytes_of_words_push<W: Word>(words: Seq<W>, w: W)
    ensures
        le_bytes_of_words(words.push(w)) == le_bytes_of_words(words) + le_bytes(w),
{
    assert(words.push(w).drop_last() =~= words);
}

/// `le_bytes_of_words` of `words` followed by `more`.
pub proof fn lemma_le_bytes_of_words_append<W: Word>(words: Seq<W>, more: Seq<W>)
    ensures
        le_bytes_of_words(words + more) == le_bytes_of_words(words) + le_bytes_of_words(more),
    decreases more.len(),
{
    if more.len() == 0 {
        assert(words + more =~= words);
        assert(le_bytes_of_words(more) =~= Seq::<u8>::empty());
        assert(le_bytes_of_words(words) + le_bytes_of_words(more) =~= le_bytes_of_words(words));
    } else {
        let m = more.drop_last();
        lemma_le_bytes_of_words_append(words, m);
        assert((words + more).drop_last() =~= words + m);
        assert((words + more).last() == more.last());
        assert(le_bytes_of_words(words) + le_bytes_of_words(m) + le_bytes(more.last())
            =~= le_bytes_of_words(words) + (le_bytes_of_words(m) + le_bytes(more.last())));
    }
}

/// Generate a `u64` using `next_u32`, little-endian order.
#[inline]
pub fn next_u64_via_u32<R: TryRng + ?Sized>(rng: &mut R) -> (res: Result<u64, R::Error>)
    ensures
        match res {
            Ok(v) => exists|mid: &R, x: u32, y: u32|
                #![trigger R::try_next_u32_post(old(rng), mid, Ok(x)), R::try_next_u32_post(mid, final(rng), Ok(y))]
                {
                    &&& R::try_next_u32_post(old(rng), mid, Ok(x))
                    &&& R::try_next_u32_post(mid, final(rng), Ok(y))
                    &&& v == ((y as u64) << 32u64) | (x as u64)
                },
            Err(e) => R::try_next_u32_post(old(rng), final(rng), Err(e)) || exists|mid: &R, x: u32|
                #![trigger R::try_next_u32_post(old(rng), mid, Ok(x)), R::try_next_u32_post(mid, final(rng), Err(e))]
                {
                    &&& R::try_next_u32_post(old(rng), mid, Ok(x))
                    &&& R::try_next_u32_post(mid, final(rng), Err(e))
                },
        },
{
    // Use LE; we explicitly generate one value before the next.
    let x = u64::from(rng.try_next_u32()?);
    let y = u64::from(rng.try_next_u32()?);
    Ok((y << 32) | x)
}

/// Fill `dst` with bytes using `next_word`
///
/// This may be used to implement `fill_bytes` over `next_u32` or
/// `next_u64`. Words are used in order of generation. The last word may be
/// partially discarded.
#[inline]
#[verifier::loop_isolation(false)]
pub fn fill_bytes_via_next_word<E, W: Word>(
    dst: &mut [u8],
    mut next_word: impl FnMut() -> Result<W, E>,
) -> (res: Result<(), E>)
    requires
        forall|| next_word.requires(()),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        match res {
            // `dst` holds the little-endian bytes of `words`, values returned by `next_word`, in
            // order; `words` has the fewest words that cover `dst`.
            Ok(()) => exists|words: Seq<W>|
                {
                    &&& forall|i: int| 0 <= i < words.len() ==> next_word.ensures((), Ok(#[trigger] words[i]))
                    &&& final(dst)@ == #[trigger] le_bytes_of_words(words).subrange(0, old(dst)@.len() as int)
                    &&& words.len() * size_of::<W>() >= old(dst)@.len()
                    &&& (words.len() == 0 || (words.len() - 1) * size_of::<W>() < old(dst)@.len())
                },
            Err(e) => next_word.ensures((), Err(e)),
        },
        // Human spec: an empty `dst` is left alone, without calling `next_word`.
        old(dst)@.len() == 0 ==> res.is_ok(),
        old(dst)@.len() == 0 ==> final(dst)@ === old(dst)@,
{
    let ghost f = next_word;
    let ghost len = dst@.len();
    proof {
        W::lemma_word();
    }
    // `dst.chunks_exact_mut(size_of::<W>())`: the chunks are `dst[pos..pos + size]`, and the
    // remainder is `dst[pos..]` after the last full chunk.
    let size = size_of::<W>();
    let mut pos = 0;
    let ghost mut words: Seq<W> = Seq::empty();
    proof {
        assert(0 * (size as int) == 0) by (nonlinear_arith);
    }
    while dst.len() - pos >= size
        invariant
            next_word == f,
            forall|| next_word.requires(()),
            size == size_of::<W>(),
            size == 4 || size == 8,
            dst@.len() == len,
            pos <= len,
            pos == words.len() * size,
            dst@.subrange(0, pos as int) == le_bytes_of_words(words),
            forall|i: int| 0 <= i < words.len() ==> f.ensures((), Ok(#[trigger] words[i])),
        decreases len - pos,
    {
        let val = next_word()?;
        let (_, chunk) = dst.split_at_mut(pos);
        let (chunk, _) = chunk.split_at_mut(size);
        chunk.copy_from_slice(val.to_le_bytes().as_ref());
        proof {
            lemma_le_bytes_of_words_push(words, val);
            let n = words.len() as int;
            let s = size as int;
            assert(n * s + s == (n + 1) * s) by (nonlinear_arith);
            words = words.push(val);
            assert(dst@.subrange(0, pos + size) =~= le_bytes_of_words(words));
        }
        pos += size;
    }
    let (_, rem) = dst.split_at_mut(pos);
    if !rem.is_empty() {
        let val = next_word()?.to_le_bytes();
        rem.copy_from_slice(&val.as_ref()[0..rem.len()]);
        proof {
            assert(exists|r: Result<W, E>|
                #[trigger] f.ensures((), r) && r is Ok && r->Ok_0.spec_le_bytes() == W::spec_bytes(val));
            let r = choose|r: Result<W, E>|
                #[trigger] f.ensures((), r) && r is Ok && r->Ok_0.spec_le_bytes() == W::spec_bytes(val);
            let w = r->Ok_0;
            assert(r == Ok::<W, E>(w));
            lemma_le_bytes_of_words_push(words, w);
            let n = words.len() as int;
            let s = size as int;
            assert(n * s + s == (n + 1) * s) by (nonlinear_arith);
            words = words.push(w);
            lemma_le_bytes_of_words_len(words);
            assert(dst@ =~= le_bytes_of_words(words).subrange(0, len as int));
        }
    } else {
        proof {
            lemma_le_bytes_of_words_len(words);
            assert(dst@ =~= le_bytes_of_words(words).subrange(0, len as int));
            let n = words.len() as int;
            let s = size as int;
            assert(n > 0 ==> (n - 1) * s == n * s - s) by (nonlinear_arith);
        }
    }
    Ok(())
}

/// Generate a `u32` or `u64` word using `fill_bytes`
pub fn next_word_via_fill<W: Word, R: TryRng>(rng: &mut R) -> (res: Result<W, R::Error>)
    ensures
        match res {
            // The little-endian bytes of the word are the bytes that `try_fill_bytes` wrote.
            Ok(w) => exists|dst_pre: Seq<u8>, dst_post: Seq<u8>|
                {
                    &&& #[trigger] R::try_fill_bytes_post(old(rng), final(rng), dst_pre, dst_post, Ok(()))
                    &&& dst_pre.len() == size_of::<W>()
                    &&& dst_post == le_bytes(w)
                },
            Err(e) => exists|dst_pre: Seq<u8>, dst_post: Seq<u8>|
                #[trigger] R::try_fill_bytes_post(old(rng), final(rng), dst_pre, dst_post, Err(e)),
        },
{
    proof {
        W::lemma_word();
    }
    let mut buf: W::Bytes = Default::default();
    let ghost buf0 = buf;
    rng.try_fill_bytes(W::bytes_as_mut(&mut buf))?;
    proof {
        assert(R::try_fill_bytes_post(old(rng), rng, W::spec_bytes(buf0), W::spec_bytes(buf), Ok(())));
    }
    Ok(W::from_le_bytes(buf))
}

/// Reads an array of words from a byte slice
///
/// Words are read from `src` in order, using LE conversion from bytes.
///
/// # Panics
///
/// Panics if `size_of_val(src) != size_of::<[W; N]>()`.
#[inline(always)]
#[verifier::loop_isolation(false)]
pub fn read_words<W: Word, const N: usize>(src: &[u8]) -> (r: [W; N])
    requires
        src@.len() == N * size_of::<W>(),
    ensures
        le_bytes_of_words(r@) == src@,
        // Human spec: each word is decoded from its corresponding input bytes in little-endian
        // order. (The developer's precondition, `src@.len() == vstd::layout::size_of::<[W; N]>()`,
        // cannot be established by any caller: see SPEC_REVIEW.md, H2.)
        r@.len() == N,
        forall|i: int|
            0 <= i < N as int ==> r@[i] == W::spec_from_le_bytes(
                src@.subrange(
                    i * vstd::layout::size_of::<W>() as int,
                    (i + 1) * vstd::layout::size_of::<W>() as int,
                ),
            ),
{
    crate::trusted::check_read_words_len::<W, N>(src);
    proof {
        W::lemma_word();
        W::lemma_spec_from_le_bytes();
    }
    let mut dst = [W::from_usize(0); N];
    // `dst.iter_mut().zip(src.chunks_exact(size_of::<W>()))`: `src` has exactly `N` chunks
    // (checked above), the `i`-th is `src[i * size..(i + 1) * size]`.
    let size = size_of::<W>();
    let mut i = 0;
    proof {
        assert(0 * (size as int) == 0) by (nonlinear_arith);
        assert(dst@.subrange(0, 0) =~= Seq::<W>::empty());
        assert(src@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while i < N
        invariant
            size == size_of::<W>(),
            size == 4 || size == 8,
            src@.len() == N * size,
            i <= N,
            le_bytes_of_words(dst@.subrange(0, i as int)) == src@.subrange(0, i * size),
            forall|j: int|
                0 <= j < i ==> dst@[j] == W::spec_from_le_bytes(
                    src@.subrange(j * size, (j + 1) * size),
                ),
            vstd::layout::size_of::<W>() == size,
            forall|w: W| #[trigger] W::spec_from_le_bytes(w.spec_le_bytes()) == w,
        decreases N - i,
    {
        proof {
            let (a, s, n) = (i as int, size as int, N as int);
            assert((a + 1) * s <= n * s) by (nonlinear_arith)
                requires
                    a < n,
                    s >= 0,
            ;
            assert((a + 1) * s == a * s + s) by (nonlinear_arith);
            assert(src@.len() == src.len());
        }
        let chunk = &src[i * size..(i + 1) * size];
        let mut buf: W::Bytes = Default::default();
        W::bytes_as_mut(&mut buf).copy_from_slice(chunk);
        let ghost dst_old = dst@;
        dst[i] = W::from_le_bytes(buf);
        proof {
            assert(dst@.subrange(0, i as int) =~= dst_old.subrange(0, i as int));
            assert(dst@.subrange(0, i + 1) =~= dst@.subrange(0, i as int).push(dst@[i as int]));
            lemma_le_bytes_of_words_push(dst@.subrange(0, i as int), dst@[i as int]);
            assert(src@.subrange(0, (i + 1) * size) =~= src@.subrange(0, i * size) + chunk@);
            // the developer's clause: the new word decodes its chunk
            assert(W::spec_from_le_bytes(dst@[i as int].spec_le_bytes()) == dst@[i as int]);
        }
        i += 1;
    }
    proof {
        assert(dst@.subrange(0, N as int) =~= dst@);
        assert(src@.subrange(0, N * size) =~= src@);
    }
    dst
}

} // verus!
