//! H2: the precondition of the developer's `read_words`,
//! `src@.len() == vstd::layout::size_of::<[W; N]>()`, cannot be established: vstd does not state the
//! size of an array, not even for concrete types. Fails with "postcondition not satisfied".

use vstd::prelude::*;

verus! {

proof fn size_of_u32_array()
    ensures
        vstd::layout::size_of::<[u32; 2]>() == 8,
{
}

fn main() {
}

} // verus!
