//! H1: the developer's `BlockRng` contracts do not compose. Verified against the developer's crate
//! (`../../../verus_human_written_spec/`); both calls fail with "precondition not satisfied".

use rand_core::block::{BlockRng, Generator};
use vstd::prelude::*;

verus! {

pub struct Zeros;

impl Generator for Zeros {
    type Output = [u32; 4];

    fn generate(&mut self, output: &mut [u32; 4]) {
        *output = [0u32; 4];
    }
}

/// `next_word` on a new `BlockRng`.
fn new_then_next_word() {
    let mut rng = BlockRng::new(Zeros);
    let _ = rng.next_word();
}

/// `remaining_results` on a reconstructed `BlockRng`.
fn reconstruct_then_remaining_results() {
    let rest: [u32; 2] = [7, 8];
    match BlockRng::<Zeros>::reconstruct(Zeros, &rest) {
        Some(rng) => {
            let _ = rng.remaining_results();
        },
        None => {},
    }
}

fn main() {
}

} // verus!
