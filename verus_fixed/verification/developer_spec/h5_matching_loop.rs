//! H5: the developer's postconditions of `next_word` form a matching loop. One call, then an
//! assertion that should simply fail: against the developer's crate the solver runs out of
//! resources; against the fixed crate (`h5_control.rs`) the assertion fails at once.

use rand_core::block::{BlockRng, Generator};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::TryFromSpec;

verus! {

pub struct Zeros;

impl Generator for Zeros {
    type Output = [u32; 4];

    fn generate(&mut self, output: &mut [u32; 4]) {
        *output = [0u32; 4];
    }
}

fn one_call(rng: &mut BlockRng<Zeros>)
    requires
        u32::try_from_spec(2usize) === Ok(old(rng).spec_results()@[0]),
{
    let _ = rng.next_word();
    assert(false);
}

fn main() {
}

} // verus!
