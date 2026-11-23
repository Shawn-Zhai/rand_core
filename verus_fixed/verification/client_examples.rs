//! A verified client of the annotated `rand_core` (not part of the crate).
//!
//! It is verified against the crate's exported specifications (`verify.sh`), so it sees what a
//! downstream verified crate sees: public specifications only, closed ones opaque. It checks that
//! the contracts can be met by implementations (`Counter`, `Constant`) and that they are precise
//! enough to determine concrete results.

use rand_core::block::{BlockRng, Generator};
use rand_core::utils;
use rand_core::{Infallible, Rng, TryRng, UnwrapErr};
use vstd::prelude::*;

verus! {

// ===== `BlockRng` =====

/// A block generator whose blocks count up from `counter`.
pub struct Counter {
    pub counter: u32,
}

pub open spec fn add(x: u32, y: u32) -> u32 {
    vstd::wrapping::u32_specs::wrapping_add(x, y)
}

impl Generator for Counter {
    type Output = [u32; 4];

    open spec fn generate_post(pre: &Self, post: &Self, output: &[u32; 4]) -> bool {
        &&& output@ == seq![pre.counter, add(pre.counter, 1), add(pre.counter, 2), add(pre.counter, 3)]
        &&& post.counter == add(pre.counter, 4)
    }

    fn generate(&mut self, output: &mut [u32; 4]) {
        output[0] = self.counter;
        output[1] = self.counter.wrapping_add(1);
        output[2] = self.counter.wrapping_add(2);
        output[3] = self.counter.wrapping_add(3);
        self.counter = self.counter.wrapping_add(4);
        proof {
            let c = old(self).counter;
            assert(output@ =~= seq![c, add(c, 1), add(c, 2), add(c, 3)]);
        }
    }
}

/// `blocks_words` has `N` words per block.
proof fn lemma_blocks_words_len<W: utils::Word, const N: usize, G: Generator<Output = [W; N]>>(
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

/// Consuming at most the words left in the buffer generates nothing.
proof fn lemma_consume_buffered<W: utils::Word, const N: usize, G: Generator<Output = [W; N]>>(
    r0: &BlockRng<G>,
    r1: &BlockRng<G>,
    k: nat,
    words: Seq<W>,
)
    requires
        k <= r0.buffer().len(),
        r0.consumes(r1, k, words),
    ensures
        words == r0.buffer().subrange(0, k as int),
        r1.buffer() == r0.buffer().subrange(k as int, r0.buffer().len() as int),
        r1.spec_core() == r0.spec_core(),
{
    let (cores, blocks) = choose|cores: Seq<G>, blocks: Seq<[W; N]>|
        {
            let stream = r0.buffer() + BlockRng::<G>::blocks_words(blocks);
            &&& #[trigger] BlockRng::<G>::generates(cores, blocks)
            &&& cores[0] == r0.spec_core()
            &&& cores.last() == r1.spec_core()
            &&& k <= stream.len()
            &&& (blocks.len() > 0 ==> stream.len() - N < k)
            &&& words == stream.subrange(0, k as int)
            &&& r1.buffer() == stream.subrange(k as int, stream.len() as int)
        };
    lemma_blocks_words_len::<W, N, G>(blocks);
    assert(blocks.len() == 0) by {
        if blocks.len() > 0 {
            assert(blocks.len() * N >= N) by (nonlinear_arith)
                requires
                    blocks.len() > 0,
            ;
        }
    }
    let stream = r0.buffer() + BlockRng::<G>::blocks_words(blocks);
    assert(stream =~= r0.buffer());
}

/// Consuming `1..=N` words from an exhausted buffer generates exactly one block.
proof fn lemma_consume_one_block<W: utils::Word, const N: usize, G: Generator<Output = [W; N]>>(
    r0: &BlockRng<G>,
    r1: &BlockRng<G>,
    k: nat,
    words: Seq<W>,
) -> (block: [W; N])
    requires
        r0.buffer().len() == 0,
        1 <= k <= N,
        r0.consumes(r1, k, words),
    ensures
        G::generate_post(&r0.spec_core(), &r1.spec_core(), &block),
        words == block@.subrange(0, k as int),
        r1.buffer() == block@.subrange(k as int, N as int),
{
    let (cores, blocks) = choose|cores: Seq<G>, blocks: Seq<[W; N]>|
        {
            let stream = r0.buffer() + BlockRng::<G>::blocks_words(blocks);
            &&& #[trigger] BlockRng::<G>::generates(cores, blocks)
            &&& cores[0] == r0.spec_core()
            &&& cores.last() == r1.spec_core()
            &&& k <= stream.len()
            &&& (blocks.len() > 0 ==> stream.len() - N < k)
            &&& words == stream.subrange(0, k as int)
            &&& r1.buffer() == stream.subrange(k as int, stream.len() as int)
        };
    lemma_blocks_words_len::<W, N, G>(blocks);
    assert(blocks.len() == 1) by {
        if blocks.len() == 0 {
        } else if blocks.len() >= 2 {
            assert(blocks.len() * N >= 2 * N) by (nonlinear_arith)
                requires
                    blocks.len() >= 2,
            ;
        }
    }
    assert(blocks.drop_last() =~= Seq::<[W; N]>::empty());
    assert(BlockRng::<G>::blocks_words(blocks.drop_last()) =~= Seq::<W>::empty());
    let stream = r0.buffer() + BlockRng::<G>::blocks_words(blocks);
    assert(stream =~= blocks[0]@);
    assert(G::generate_post(&cores[0], &cores[1], &blocks[0]));
    blocks[0]
}

/// The little-endian bytes of 12 and 13.
proof fn lemma_le_bytes_small()
    ensures
        utils::le_bytes(12u32) == seq![12u8, 0u8, 0u8, 0u8],
        utils::le_bytes(13u32) == seq![13u8, 0u8, 0u8, 0u8],
{
    utils::lemma_le_bytes_u32(12u32);
    utils::lemma_le_bytes_u32(13u32);
    assert(seq![
        (12u32 & 0xff) as u8,
        ((12u32 >> 8u32) & 0xff) as u8,
        ((12u32 >> 16u32) & 0xff) as u8,
        ((12u32 >> 24u32) & 0xff) as u8,
    ] =~= seq![12u8, 0u8, 0u8, 0u8]) by (compute_only);
    assert(seq![
        (13u32 & 0xff) as u8,
        ((13u32 >> 8u32) & 0xff) as u8,
        ((13u32 >> 16u32) & 0xff) as u8,
        ((13u32 >> 24u32) & 0xff) as u8,
    ] =~= seq![13u8, 0u8, 0u8, 0u8]) by (compute_only);
}

/// A new `BlockRng` over `Counter { counter: 10 }`: two `next_word`s, a 6-byte `fill_bytes`, then
/// `next_u64_from_u32`. Each result is determined by the contracts.
fn example_block_rng() {
    let mut rng = BlockRng::new(Counter { counter: 10 });
    let ghost r0 = rng;

    // First word: the buffer is empty, so one block [10, 11, 12, 13] is generated.
    let a = rng.next_word();
    let ghost r1 = rng;
    proof {
        let b = lemma_consume_one_block::<u32, 4, Counter>(&r0, &r1, 1, seq![a]);
        assert(seq![a][0] == b@[0]);
    }
    assert(a == 10);

    // Second word: from the buffer [11, 12, 13]; nothing is generated.
    let b = rng.next_word();
    let ghost r2 = rng;
    proof {
        lemma_consume_buffered::<u32, 4, Counter>(&r1, &r2, 1, seq![b]);
        assert(seq![b][0] == r1.buffer()[0]);
    }
    assert(b == 11);

    // 6 bytes: words 12 and 13, the second one partially; the buffer is then empty.
    let mut dest = [0u8; 6];
    rng.fill_bytes(&mut dest);
    let ghost r3 = rng;
    proof {
        lemma_le_bytes_small();
        let (k, words) = choose|k: nat, words: Seq<u32>|
            {
                &&& #[trigger] r2.consumes(&r3, k, words)
                &&& dest@ == utils::le_bytes_of_words(words).subrange(0, 6)
                &&& k * size_of::<u32>() >= 6
                &&& (k == 0 || (k - 1) * size_of::<u32>() < 6)
            };
        assert(k == 2);
        lemma_consume_buffered::<u32, 4, Counter>(&r2, &r3, k, words);
        assert(words =~= seq![12u32, 13u32]);
        reveal_with_fuel(utils::le_bytes_of_words, 3);
        assert(seq![12u32, 13u32].drop_last().drop_last() =~= Seq::<u32>::empty());
        assert(dest@ =~= (utils::le_bytes(12u32) + utils::le_bytes(13u32)).subrange(0, 6));
        assert(r3.buffer().len() == 0);
    }
    assert(dest[0] == 12 && dest[1] == 0 && dest[4] == 13 && dest[5] == 0);

    // A u64 from two words: the buffer is exhausted, so block [14, 15, 16, 17] is generated.
    let c = rng.next_u64_from_u32();
    let ghost r4 = rng;
    proof {
        let words = choose|words: Seq<u32>|
            #[trigger] r3.consumes(&r4, 2, words) && c == ((words[1] as u64) << 32u64) | (
            words[0] as u64);
        let blk = lemma_consume_one_block::<u32, 4, Counter>(&r3, &r4, 2, words);
        assert(words[0] == 14 && words[1] == 15);
        assert((((15u32 as u64) << 32u64) | (14u32 as u64)) == 0x0000_000f_0000_000eu64) by (bit_vector);
    }
    assert(c == 0x0000_000f_0000_000e);
}

// ===== `utils` =====

/// `read_words` decodes little-endian words.
fn example_read_words() {
    let bytes: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    let w: [u32; 2] = utils::read_words(&bytes);
    proof {
        reveal_with_fuel(utils::le_bytes_of_words, 3);
        assert(w@.drop_last().drop_last() =~= Seq::<u32>::empty());
        assert(utils::le_bytes(w[0]) + utils::le_bytes(w[1]) =~= bytes@);
        let (x, y) = (w[0], w[1]);
        utils::lemma_le_bytes_u32(x);
        utils::lemma_le_bytes_u32(y);
        assert(utils::le_bytes(x) =~= bytes@.subrange(0, 4));
        assert(utils::le_bytes(y) =~= bytes@.subrange(4, 8));
        assert(x == 0x0403_0201) by (bit_vector)
            requires
                (x & 0xff) as u8 == 1u8,
                ((x >> 8u32) & 0xff) as u8 == 2u8,
                ((x >> 16u32) & 0xff) as u8 == 3u8,
                ((x >> 24u32) & 0xff) as u8 == 4u8,
        ;
        assert(y == 0x0807_0605) by (bit_vector)
            requires
                (y & 0xff) as u8 == 5u8,
                ((y >> 8u32) & 0xff) as u8 == 6u8,
                ((y >> 16u32) & 0xff) as u8 == 7u8,
                ((y >> 24u32) & 0xff) as u8 == 8u8,
        ;
    }
    assert(w[0] == 0x0403_0201 && w[1] == 0x0807_0605);
}

// ===== `TryRng`, `Rng`, `UnwrapErr` =====

/// A generator that always returns `self.0`.
pub struct Constant(pub u32);

impl TryRng for Constant {
    type Error = Infallible;

    open spec fn try_next_u32_post(pre: &Self, post: &Self, res: Result<u32, Infallible>) -> bool {
        res == Ok::<u32, Infallible>(pre.0) && post == pre
    }

    open spec fn try_next_u64_post(pre: &Self, post: &Self, res: Result<u64, Infallible>) -> bool {
        res == Ok::<u64, Infallible>(((pre.0 as u64) << 32u64) | (pre.0 as u64)) && post == pre
    }

    open spec fn try_fill_bytes_post(
        pre: &Self,
        post: &Self,
        dst_pre: Seq<u8>,
        dst_post: Seq<u8>,
        res: Result<(), Infallible>,
    ) -> bool {
        res is Ok && post == pre && dst_post.len() == dst_pre.len()
    }

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        Ok(self.0)
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        Ok(((self.0 as u64) << 32) | (self.0 as u64))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        Ok(())
    }
}

/// `next_u64_via_u32`'s contract determines its result from `try_next_u32`'s. (Verus does not
/// allow calling it from `Constant`'s own `try_next_u64`, as upstream's tests do for their RNG:
/// that would be a cycle through the `TryRng` impl being defined.)
fn example_next_u64_via_u32() {
    let mut c = Constant(0x8000_0001);
    let r = utils::next_u64_via_u32(&mut c);
    assert(r matches Ok(v) && v == ((0x8000_0001u32 as u64) << 32u64) | (0x8000_0001u32 as u64));
}

/// `UnwrapErr` passes the wrapped generator's values through, and `Rng`'s blanket
/// implementation unwraps them.
fn example_unwrap_err() {
    let mut rng = UnwrapErr(Constant(7));
    let x = rng.next_u32();
    assert(x == 7);
    let y = rng.next_u64();
    assert(y == ((7u32 as u64) << 32u64) | (7u32 as u64));
}

fn main() {
}

} // verus!
