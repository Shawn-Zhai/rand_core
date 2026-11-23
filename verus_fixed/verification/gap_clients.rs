//! Calls that the fixed contracts allow and Claude's first-pass contracts do not (not part of
//! the crate). Each is valid upstream code. Against the fixed crate all of them verify
//! (`verify.sh`); against Claude's first pass (`../verus`), each of the four fails, as recorded in
//! SPEC_REVIEW.md (`negative_controls.py --first-pass` runs both).

use rand_core::block::{BlockRng, Generator};
use rand_core::{Rng, TryRng, UnwrapErr};
use vstd::prelude::*;

verus! {

/// A block generator of zeros.
#[derive(Clone)]
pub struct Zeros;

impl Generator for Zeros {
    type Output = [u32; 4];

    open spec fn generate_post(pre: &Self, post: &Self, output: &[u32; 4]) -> bool {
        output@ == seq![0u32, 0u32, 0u32, 0u32]
    }

    fn generate(&mut self, output: &mut [u32; 4]) {
        *output = [0u32; 4];
        proof {
            assert(output@ =~= seq![0u32, 0u32, 0u32, 0u32]);
        }
    }
}

/// A1: `fill_bytes` leaves `dst` its length (first pass: unknown to the caller).
fn gap_fill_bytes_len<R: Rng>(rng: &mut R, dst: &mut [u8])
    requires
        old(dst)@.len() == 4,
{
    rng.fill_bytes(dst);
    assert(dst@.len() == 4);
}

/// A2: `UnwrapErr::re` reborrows the same generator (first pass: no contract).
fn gap_re<R: TryRng>(u: &mut UnwrapErr<&mut R>) {
    let ghost before = *u.0;
    let v = u.re();
    assert(*v.0 == before);
}

/// A3: `reconstruct` with an empty block returns `None` upstream (first pass: requires `N > 0`).
pub struct Empty;

impl Generator for Empty {
    type Output = [u32; 0];

    open spec fn generate_post(pre: &Self, post: &Self, output: &[u32; 0]) -> bool {
        true
    }

    fn generate(&mut self, output: &mut [u32; 0]) {
    }
}

fn gap_reconstruct_empty_block() {
    let r = BlockRng::<Empty>::reconstruct(Empty, &[]);
    assert(r is None);
}

/// A4: `reset_and_skip` makes any `BlockRng` well-formed, e.g. a clone, whose state Verus does not
/// know (the derived `Clone` has no contract). First pass: requires the clone to be well-formed.
fn gap_reset_clone(rng: &BlockRng<Zeros>) {
    let mut c = rng.clone();
    c.reset_and_skip(0);
    let x = c.next_word();
}

fn main() {
}

} // verus!
