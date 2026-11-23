//! The control for `h5_matching_loop.rs`: the same client against the fixed crate, whose
//! `next_word` states the developer's clauses with `index_is` triggers. The assertion fails at once.

use rand_core::block::{BlockRng, Generator};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::TryFromSpec;

verus! {

pub struct Zeros;

impl Generator for Zeros {
    type Output = [u32; 4];

    open spec fn generate_post(pre: &Self, post: &Self, output: &[u32; 4]) -> bool {
        true
    }

    fn generate(&mut self, output: &mut [u32; 4]) {
        *output = [0u32; 4];
    }
}

fn one_call(rng: &mut BlockRng<Zeros>)
    requires
        u32::try_from_spec(2usize) === Ok(old(rng).spec_results()@[0]),
{
    proof {
        rng.lemma_wf_human();
    }
    let _ = rng.next_word();
    assert(false);
}

fn main() {
}

} // verus!
