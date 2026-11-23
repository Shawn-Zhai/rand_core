// Proof hints for `compare_specs.py` on rand_core (`verus_fixed/` against
// `verus_human_written_spec/`). Each hint only calls lemmas of the verified crate or asserts
// facts that Verus then proves; nothing is assumed.
//
// Two bridges are needed between the developer's vocabulary and the crate's:
//   * the developer states "N fits in W" and "the index stored in `results[0]` is i" with
//     `W::try_from_spec(..)`; the crate's contracts use `W::spec_max()` and the closed `wf()`.
//     `Sealed::lemma_try_from_usize` and `BlockRng::lemma_wf_human` relate them.
//   * the crate states the developer's index clauses with `index_is(x, i)`, an open spec function
//     equal to the developer's `W::try_from_spec(i as usize) === Ok(x)`, so that its
//     postconditions do not form a matching loop. To prove a developer clause from the crate's,
//     the hints name `index_is` for the index at hand.

// @hint claude_implies_gold__BlockRng__new before
proof {
    // `W::try_from_spec(N).is_ok()` is `N <= W::spec_max()`
    W::lemma_try_from_usize(N, vstd::pervasive::arbitrary());
}

// @hint claude_implies_gold__BlockRng__next_word before
proof {
    // the developer's precondition is `wf()`
    slf.lemma_wf_human();
}

// @hint claude_implies_gold__BlockRng__next_word after
proof {
    assert forall|i: int|
        0 <= i < N as int && #[trigger] W::try_from_spec(i as usize) === Ok(pre.spec_results()@[0]) implies {
        &&& ret == pre.spec_results()@[i]
        &&& slf.spec_core() === pre.spec_core()
        &&& W::try_from_spec((i + 1) as usize) === Ok(slf.spec_results()@[0])
        &&& forall|j: int| 1 <= j < N as int ==> slf.spec_results()@[j] == pre.spec_results()@[j]
    } by {
        assert(crate::block::index_is(pre.spec_results()@[0], i));
    }
    assert(crate::block::index_is(pre.spec_results()@[0], N as int) ==> crate::block::index_is(
        slf.spec_results()@[0],
        1,
    ));
}

// @hint claude_implies_gold__BlockRng__fill_bytes before
proof {
    slf.lemma_wf_human();
}

// @hint claude_implies_gold__BlockRng__fill_bytes after
proof {
    let size = vstd::layout::size_of::<W>() as int;
    assert forall|i: int|
        1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(pre.spec_results()@[0])
            && dest@.len() as int <= (N as int - i) * size implies {
        &&& slf.spec_core() === pre.spec_core()
        &&& forall|j: int| 1 <= j < N as int ==> slf.spec_results()@[j] == pre.spec_results()@[j]
        &&& W::try_from_spec((i + (dest@.len() as int + size - 1) / size) as usize) === Ok(slf.spec_results()@[0])
    } by {
        assert(crate::block::index_is(pre.spec_results()@[0], i));
    }
    assert forall|i: int|
        1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(pre.spec_results()@[0])
            && dest@.len() as int > (N as int - i) * size implies {
        let words = ((dest@.len() as int - (N as int - i) * size) + size - 1) / size;
        W::try_from_spec((((words - 1) % N as int) + 1) as usize) === Ok(slf.spec_results()@[0])
    } by {
        assert(crate::block::index_is(pre.spec_results()@[0], i));
    }
}

// @hint claude_implies_gold__BlockRng__next_u64_from_u32 before
proof {
    // the developer's precondition (with `N <= u32::MAX`) is `wf()`
    slf.lemma_wf_human();
}
