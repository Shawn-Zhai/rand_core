use crate::{Rng, TryRng};
use vstd::prelude::*;

verus! {

/// A random number generator that can be explicitly seeded.
///
/// This trait encapsulates the low-level functionality common to all
/// pseudo-random number generators (PRNGs, or algorithmic generators).
///
/// A generator implementing `SeedableRng` will usually be deterministic, but
/// beware that portability and reproducibility of results **is not implied**.
/// Refer to documentation of the generator, noting that generators named after
/// a specific algorithm are usually tested for reproducibility against a
/// reference vector, while `SmallRng` and `StdRng` specifically opt out of
/// reproducibility guarantees.
pub trait SeedableRng: Sized {
    /// Seed type, which is restricted to types mutably-dereferenceable as `u8`
    /// arrays (we recommend `[u8; N]` for some `N`).
    ///
    /// It is recommended to seed PRNGs with a seed of at least circa 100 bits,
    /// which means an array of `[u8; 12]` or greater to avoid picking RNGs with
    /// partially overlapping periods.
    ///
    /// For cryptographic RNG's a seed of 256 bits is recommended, `[u8; 32]`.
    ///
    ///
    /// # Implementing `SeedableRng` for RNGs with large seeds
    ///
    /// Note that [`Default`] is not implemented for large arrays `[u8; N]` with
    /// `N` > 32. To be able to implement the traits required by `SeedableRng`
    /// for RNGs with such large seeds, the newtype pattern can be used:
    ///
    /// ```
    /// use rand_core::SeedableRng;
    ///
    /// const N: usize = 64;
    /// #[derive(Clone)]
    /// pub struct MyRngSeed(pub [u8; N]);
    /// # #[allow(dead_code)]
    /// pub struct MyRng(MyRngSeed);
    ///
    /// impl Default for MyRngSeed {
    ///     fn default() -> MyRngSeed {
    ///         MyRngSeed([0; N])
    ///     }
    /// }
    ///
    /// impl AsRef<[u8]> for MyRngSeed {
    ///     fn as_ref(&self) -> &[u8] {
    ///         &self.0
    ///     }
    /// }
    ///
    /// impl AsMut<[u8]> for MyRngSeed {
    ///     fn as_mut(&mut self) -> &mut [u8] {
    ///         &mut self.0
    ///     }
    /// }
    ///
    /// impl SeedableRng for MyRng {
    ///     type Seed = MyRngSeed;
    ///
    ///     fn from_seed(seed: MyRngSeed) -> MyRng {
    ///         MyRng(seed)
    ///     }
    /// }
    /// ```
    type Seed: Clone + Default + AsRef<[u8]> + AsMut<[u8]>;

    /// Create a new PRNG using the given seed.
    ///
    /// PRNG implementations are allowed to assume that bits in the seed are
    /// well distributed. That means usually that the number of one and zero
    /// bits are roughly equal, and values like 0, 1 and (size - 1) are unlikely.
    /// Note that many non-cryptographic PRNGs will show poor quality output
    /// if this is not adhered to. If you wish to seed from simple numbers, use
    /// `seed_from_u64` instead.
    ///
    /// All PRNG implementations should be reproducible unless otherwise noted:
    /// given a fixed `seed`, the same sequence of output should be produced
    /// on all runs, library versions and architectures (e.g. check endianness).
    /// Any "value-breaking" changes to the generator should require bumping at
    /// least the minor version and documentation of the change.
    ///
    /// It is not required that this function yield the same state as a
    /// reference implementation of the PRNG given equivalent seed; if necessary
    /// another constructor replicating behaviour from a reference
    /// implementation can be added.
    ///
    /// PRNG implementations should make sure `from_seed` never panics. In the
    /// case that some special values (like an all zero seed) are not viable
    /// seeds it is preferable to map these to alternative constant value(s),
    /// for example `0xBAD5EEDu32` or `0x0DDB1A5E5BAD5EEDu64` ("odd biases? bad
    /// seed"). This is assuming only a small number of values must be rejected.
    fn from_seed(seed: Self::Seed) -> Self;

    /// Create a new PRNG using a `u64` seed.
    ///
    /// This is a convenience-wrapper around `from_seed` to allow construction
    /// of any `SeedableRng` from a simple `u64` value. It is designed such that
    /// low Hamming Weight numbers like 0 and 1 can be used and should still
    /// result in good, independent seeds to the PRNG which is returned.
    ///
    /// This **is not suitable for cryptography**, as should be clear given that
    /// the input size is only 64 bits.
    ///
    /// Implementations for PRNGs *may* provide their own implementations of
    /// this function, but the default implementation should be good enough for
    /// all purposes. *Changing* the implementation of this function should be
    /// considered a value-breaking change.
    fn seed_from_u64(mut state: u64) -> Self {
        let ghost state0 = state;
        let mut seed = Self::Seed::default();
        // `seed.as_mut().chunks_exact_mut(4)`: the chunks are `dst[pos..pos + 4]`, and the
        // remainder is `dst[pos..]` after the last full chunk.
        let dst = seed.as_mut();
        let ghost len = dst@.len();
        let mut pos = 0;
        let ghost mut n: nat = 0;
        while dst.len() - pos >= 4
            invariant
                pos <= len,
                dst@.len() == len,
                pos == 4 * n,
                state == pcg32_state(state0, n),
                dst@.subrange(0, pos as int) == pcg32_bytes(state0, n),
            decreases len - pos,
        {
            let (_, chunk) = dst.split_at_mut(pos);
            let (chunk, _) = chunk.split_at_mut(4);
            chunk.copy_from_slice(&pcg32(&mut state));
            pos += 4;
            proof {
                n = n + 1;
                assert(dst@.subrange(0, pos as int) =~= pcg32_bytes(state0, n));
            }
        }
        let (_, rem) = dst.split_at_mut(pos);
        if !rem.is_empty() {
            rem.copy_from_slice(&pcg32(&mut state)[0..rem.len()]);
            proof {
                n = n + 1;
            }
        }
        proof {
            // The seed is the output of PCG32 from `state`: `n` outputs, little-endian, truncated
            // to the length of the seed. `n` is the smallest number of outputs that covers the
            // seed.
            assert(dst@ =~= pcg32_bytes(state0, n).subrange(0, len as int));
            assert(4 * n >= len && (n == 0 || 4 * (n - 1) < len));
        }

        Self::from_seed(seed)
    }

    /// Create a new PRNG seeded from an infallible `Rng`.
    ///
    /// This may be useful when needing to rapidly seed many PRNGs from a master
    /// PRNG, and to allow forking of PRNGs. It may be considered deterministic.
    ///
    /// The master PRNG should be at least as high quality as the child PRNGs.
    /// When seeding non-cryptographic child PRNGs, we recommend using a
    /// different algorithm for the master PRNG (ideally a CSPRNG) to avoid
    /// correlations between the child PRNGs. If this is not possible (e.g.
    /// forking using small non-crypto PRNGs) ensure that your PRNG has a good
    /// mixing function on the output or consider use of a hash function with
    /// `from_seed`.
    ///
    /// Note that seeding `XorShiftRng` from another `XorShiftRng` provides an
    /// extreme example of what can go wrong: the new PRNG will be a clone
    /// of the parent.
    ///
    /// PRNG implementations are allowed to assume that a good RNG is provided
    /// for seeding, and that it is cryptographically secure when appropriate.
    /// As of `rand` 0.7 / `rand_core` 0.5, implementations overriding this
    /// method should ensure the implementation satisfies reproducibility
    /// (in prior versions this was not required).
    ///
    /// [`rand`]: https://docs.rs/rand
    fn from_rng<R: Rng + ?Sized>(rng: &mut R) -> Self {
        let mut seed = Self::Seed::default();
        rng.fill_bytes(seed.as_mut());
        Self::from_seed(seed)
    }

    /// Create a new PRNG seeded from a potentially fallible `Rng`.
    ///
    /// See [`from_rng`][SeedableRng::from_rng] docs for more information.
    fn try_from_rng<R: TryRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut seed = Self::Seed::default();
        rng.try_fill_bytes(seed.as_mut())?;
        Ok(Self::from_seed(seed))
    }

    /// Fork this PRNG
    ///
    /// This creates a new PRNG from the current one by initializing a new one and
    /// seeding it from the current one.
    ///
    /// This is useful when initializing a PRNG for a thread
    fn fork(&mut self) -> Self
    where
        Self: Rng,
    {
        Self::from_rng(self)
    }

    /// Fork this PRNG
    ///
    /// This creates a new PRNG from the current one by initializing a new one and
    /// seeding it from the current one.
    ///
    /// This is useful when initializing a PRNG for a thread.
    ///
    /// This is the failable equivalent to [`SeedableRng::fork`]
    fn try_fork(&mut self) -> Result<Self, Self::Error>
    where
        Self: TryRng,
    {
        Self::try_from_rng(self)
    }
}

/// (ghost) One step of the PCG32 state, a 64-bit linear congruential generator:
/// `state * MUL + INC` modulo `2^64`.
pub open spec fn pcg32_step(state: u64) -> u64 {
    ((state as nat * 0x5851_F42D_4C95_7F2D + 0xA176_54E4_6FBE_17F3) % 0x1_0000_0000_0000_0000) as u64
}

/// (ghost) The PCG32 output function ("XSH RR") applied to the state `state`.
pub open spec fn pcg32_output(state: u64) -> u32 {
    vstd::wrapping::u32_specs::rotate_right(
        (((state >> 18u64) ^ state) >> 27u64) as u32,
        (state >> 59u64) as u32,
    )
}

/// (ghost) The PCG32 state after `n` steps from `state`.
pub open spec fn pcg32_state(state: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        state
    } else {
        pcg32_step(pcg32_state(state, (n - 1) as nat))
    }
}

/// (ghost) The first `n` PCG32 outputs from `state` (each output is computed after a step), as
/// little-endian bytes.
pub open spec fn pcg32_bytes(state: u64, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        pcg32_bytes(state, (n - 1) as nat) + crate::trusted::u32_le_bytes(
            pcg32_output(pcg32_state(state, n)),
        )
    }
}

/// PCG32 generator function
fn pcg32(state: &mut u64) -> (r: [u8; 4])
    ensures
        *final(state) == pcg32_step(*old(state)),
        r@ == crate::trusted::u32_le_bytes(pcg32_output(*final(state))),
{
    const MUL: u64 = 0x5851_F42D_4C95_7F2D;
    const INC: u64 = 0xA176_54E4_6FBE_17F3;

    // We advance the state first (to get away from the input value,
    // in case it has low Hamming Weight).
    *state = state.wrapping_mul(MUL).wrapping_add(INC);
    proof {
        lemma_pcg32_step(*old(state));
    }
    let state = *state;

    // Use PCG output function with to_le to generate x:
    let xorshifted = (((state >> 18) ^ state) >> 27) as u32;
    let rot = (state >> 59) as u32;
    let x = xorshifted.rotate_right(rot);
    crate::trusted::u32_to_le_bytes(x)
}

/// Upstream's value test (`test_seed_from_u64` in `tests/mod.rs`): from state 0, the 8-byte
/// seed that `seed_from_u64` writes (two PCG32 outputs) is the little-endian encoding of
/// `5029875928683246316`. This checks the specification, including the trusted specifications
/// of `rotate_right` (vstd's) and `to_le_bytes`, against upstream's test vector.
proof fn lemma_pcg32_test_vector()
    ensures
        pcg32_bytes(0, 2) == crate::trusted::u64_le_bytes(5029875928683246316u64),
{
    let (s1, s2) = (0xa176_54e4_6fbe_17f3u64, 0xe0a2_def2_7678_daaau64);
    assert(pcg32_state(0, 1) == 0xa176_54e4_6fbe_17f3u64 && pcg32_state(0, 2)
        == 0xe0a2_def2_7678_daaau64) by (compute_only);
    assert((((0xa176_54e4_6fbe_17f3u64 >> 18u64) ^ 0xa176_54e4_6fbe_17f3u64) >> 27u64) as u32
        == 0x2ecf_973fu32) by (bit_vector);
    assert((0xa176_54e4_6fbe_17f3u64 >> 59u64) as u32 == 20u32) by (bit_vector);
    assert((((0xe0a2_def2_7678_daaau64 >> 18u64) ^ 0xe0a2_def2_7678_daaau64) >> 27u64) as u32
        == 0x145c_db58u32) by (bit_vector);
    assert((0xe0a2_def2_7678_daaau64 >> 59u64) as u32 == 28u32) by (bit_vector);
    assert(((0x2ecf_973fu32 >> 20u32) | (0x2ecf_973fu32 << 12u32)) == 0xf973_f2ecu32) by (bit_vector);
    assert(((0x145c_db58u32 >> 28u32) | (0x145c_db58u32 << 4u32)) == 0x45cd_b581u32) by (bit_vector);
    assert(pcg32_output(s1) == 0xf973_f2ecu32);
    assert(pcg32_output(s2) == 0x45cd_b581u32);
    reveal_with_fuel(pcg32_bytes, 3);
    assert(crate::trusted::u32_le_bytes(0xf973_f2ecu32) + crate::trusted::u32_le_bytes(0x45cd_b581u32)
        =~= crate::trusted::u64_le_bytes(5029875928683246316u64)) by (compute_only);
    assert(pcg32_bytes(0, 0) =~= Seq::<u8>::empty());
    assert(pcg32_bytes(0, 2) =~= crate::trusted::u32_le_bytes(0xf973_f2ecu32)
        + crate::trusted::u32_le_bytes(0x45cd_b581u32));
}

/// The wrapping arithmetic of `pcg32` computes `pcg32_step`.
proof fn lemma_pcg32_step(s: u64)
    ensures
        vstd::wrapping::u64_specs::wrapping_add(
            vstd::wrapping::u64_specs::wrapping_mul(s, 0x5851_F42D_4C95_7F2D),
            0xA176_54E4_6FBE_17F3,
        ) == pcg32_step(s),
{
    let d: int = 0x1_0000_0000_0000_0000;
    let p: int = s as int * 0x5851_F42D_4C95_7F2D;
    let i: int = 0xA176_54E4_6FBE_17F3;
    let m: int = p % d;
    vstd::arithmetic::div_mod::lemma_mod_bound(p, d);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(p, i, d);
    vstd::arithmetic::div_mod::lemma_small_mod(i as nat, d as nat);
    if m + i >= d {
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(m + i - d, d);
        vstd::arithmetic::div_mod::lemma_small_mod((m + i - d) as nat, d as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_small_mod((m + i) as nat, d as nat);
    }
}

} // verus!
