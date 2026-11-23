# Review: Claude's verified spec against the developer's spec (2026-11-23)

**Inputs.** "Claude's spec" is the specifications and proofs in [`../verus/src/`](../verus/src/) (first
pass, 2026-11-18, ported to Verus 0.2026.11.22 in commit 5e29379). "The developer's spec" is
[`../verus_human_written_spec/src/`](../verus_human_written_spec/src/), the compilable version (commit
f5fc9db). The developer's spec was the reference, and both were read as possibly wrong. Disagreements were
settled by running Verus whenever possible. This folder is a copy of `verus/` with the amendments applied;
[`amendments.diff`](amendments.diff) shows every hand edit against `verus/`. `verus/` and
`verus_human_written_spec/` are unchanged.

Tooling: Verus 0.2026.11.22.1ce6a59 (bare binary, bundled vstd), as in Claude's port; rustc 1.100.0 for
the normal build.

## Outcome

**Claude's verified contracts contain no false statement**, and where both specs say something, Claude's
usually says more: it describes the words and bytes that `BlockRng` returns, where the developer's spec
describes only how the index moves. But Claude's spec has **gaps the developer's spec does not**:

| # | Problem in Claude's spec | Developer's spec | Amendment |
|---|---|---|---|
| C1 | `TryRng::try_fill_bytes` and `Rng::fill_bytes` do not promise that `dst` keeps its length | `final(dst)@.len() == old(dst)@.len()` | added to both trait contracts |
| C2 | `reconstruct` requires `0 < N <= W::MAX`; upstream needs that only when it builds a result. Claude's report says upstream panics for `N == 0`: false, it returns `None` | `remaining_results.len() < N ==> W::try_from_spec(N).is_ok()` | developer's precondition |
| C3 | `reset_and_skip` requires `old(self).wf()`, but never reads the old index. A `BlockRng` whose state Verus does not know (a clone: the derived `Clone` has no contract) can never be used again | no requirement on the index | developer's precondition; `reset_and_skip` now makes any `BlockRng` well-formed |
| C4 | `UnwrapErr::re` has no contract | the result reborrows the same generator | developer's contract (verifies with the body unchanged) |
| C5 | `next_word`, `next_u64_from_u32`, `fill_bytes`, `reset_and_skip(0)` say nothing about the words already consumed, so they allow overwriting them, and an empty `fill_bytes` may change the state | the other words of the buffer are unchanged; an empty `fill_bytes` leaves the state alone | developer's clauses added |
| C6 | `fill_bytes_via_next_word` allows an error for an empty `dst` | `dst.len() == 0 ==> Ok`, `dst` unchanged | developer's clauses added |
| C7 | two inaccurate statements in `VERIFICATION.md` (below) | — | corrected in this folder's `VERIFICATION.md` |

Each gap is shown by Verus, not only by reading. Mutants M23–M27 change the code's behaviour in ways that
only the developer's clauses rule out. All five verify on Claude's crate and are rejected by the fixed crate. Four
valid calls (`gap_clients.rs`) fail against Claude's crate and verify against the fixed crate.

**The developer's spec has mistakes too** (H1–H5 below; their folder is unchanged). The most serious are
H1 and H5. H1: its `BlockRng` contracts do not compose, so no client can call `next_word` on a `BlockRng`
from `new`. H5: its quantified postconditions form a matching loop, so a client that calls `next_word` even
once exhausts the solver. Three of its preconditions are insufficient or unusable (H2–H4).

**Everything the developer's spec states is now proved of the fixed crate, except where it is wrong.**
[`verification/human_spec_client.rs`](verification/human_spec_client.rs) restates each of the developer's
13 non-trivial contracts verbatim and implements it by calling the fixed crate. It verifies with three extra
preconditions, exactly where H2–H4 say the developer's precondition does not suffice.
[`verification/claude_spec_client.rs`](verification/claude_spec_client.rs) does the same for Claude's
first-pass contracts: clients of Claude's spec keep working.

**No executable code changed.** The macro-expanded normal build of this crate is identical to `verus/`'s,
except for comments and the empty `const _: () = ();` that an erased `broadcast use` leaves.

## Verdicts by function

"Both" in the last column means that the fixed crate states the developer's clauses and Claude's, and Verus
proves both. "Equivalent" preconditions are equivalent by `lemma_wf_human` or `W::lemma_try_from_usize`.

| Function | Developer's contract | Claude's (first pass) | Verdict | Fixed crate |
|---|---|---|---|---|
| `TryRng::try_fill_bytes`, `Rng::fill_bytes` | `dst` keeps its length | the implementation's hook only | **Claude missing** (C1) | both |
| other `TryRng`, `Rng` methods; `Generator::generate` | `ensures true` | the implementation's hook | Claude stronger | unchanged |
| `UnwrapErr::re` | `*result.0` is `*self.0`, now and at the end of the borrow | none | **Claude missing** (C4) | developer's |
| `BlockRng::new` | `N > 0`, `N` fits in `W`; core | same precondition; `wf()`, empty buffer, core | Claude stronger | unchanged |
| `reconstruct` | precondition only when building a result; `None` iff too long; core | `0 < N <= W::MAX`; buffer = `remaining_results` | **Claude's precondition too strong** (C2) | developer's precondition, both postconditions |
| `reset_and_skip` | `N > 0`, `N` fits, `n < N`; for `n == 0`: core and other words unchanged | requires `wf()`; `wf()` after; `n > 0`: one block generated, buffer = its words `n..` | **Claude's precondition too strong** (C3); **Claude missing** frame (C5); Claude stronger otherwise | developer's precondition, both postconditions |
| `word_offset` | `N > 0`; `result < N` | `wf()`; the exact offset | **developer's precondition insufficient** (H4) | `wf()` or index in `1..=N`; Claude's postcondition |
| `remaining_results` | `N > 0`, index in `1..=N`; `len < N` | `wf()`; the buffer | Claude's precondition stronger by `N <= W::MAX` | `wf()` or developer's; Claude's postcondition |
| `next_word` | index in `1..=N`, `N` fits; index `i < N`: the word at `i`, core, index `i + 1`, other words unchanged; `i == N`: index 1 | `wf()` (equivalent); `consumes(old, new, 1, [r])` | **Claude missing** frame (C5); Claude stronger otherwise (what is returned after a refill) | both |
| `next_u64_from_u32` | `N >= 2`, `N <= u32::MAX`, index valid; per case: result halves, index, frame | `wf()`, `N >= 2` (equivalent); `consumes(old, new, 2, [lo, hi])`, `r == hi << 32 \| lo` | **Claude missing** frame and `r >> 32 == results[1]` after a refill (C5); Claude stronger otherwise | both |
| `BlockRng::fill_bytes` | as `next_word`; length kept; empty `dest`: state unchanged; final index (two cases, with the arithmetic) | `wf()` (equivalent); the bytes written are the next `k` words, `k = ceil(len / size)` | **Claude missing** empty-`dest` identity and frame (C5); the index cases follow from Claude's (proved); Claude stronger otherwise (the bytes) | both |
| `fill_bytes_via_next_word` | no precondition; length kept; empty `dst`: `Ok`, unchanged | `next_word` callable; bytes of the words returned; `Err` came from `next_word` | **developer's precondition insufficient** (H3); **Claude missing** empty case (C6) | Claude's precondition, both postconditions |
| `read_words` | `src.len() == size_of::<[W; N]>()`; word `i` decodes bytes `i * size..` | `src.len() == N * size_of::<W>()`; `le_bytes_of_words(r) == src` | **developer's precondition unusable** (H2); postconditions equivalent | Claude's precondition, both postconditions |
| `next_u64_via_u32`, `next_word_via_fill` | `ensures true` | the results, from the `try_*` hooks | Claude stronger | unchanged |
| `SeedableRng`, `pcg32` | `ensures true` / none | trait methods unspecified (overridable); bodies verified; `pcg32` functional, checked on upstream's test vector | Claude stronger | unchanged |
| `Generator::drop` | `ensures true` | `opens_invariants none no_unwind` (Verus requires it of `Drop` code) | different, both fine | unchanged |

## Findings in Claude's work

### C1. `try_fill_bytes` and `fill_bytes` do not promise that `dst` keeps its length (fixed)

Claude's contracts are the implementation's hook `try_fill_bytes_post(pre, post, dst_pre, dst_post, res)`,
which need not mention lengths. Verus does not know on its own that a `&mut [u8]` keeps its length: after
`rng.fill_bytes(buf)` a verified caller cannot prove `buf@.len() == 4` (`gap_fill_bytes_len` fails against
`verus/`). The fact can be recovered by calling vstd's axiom `mut_ref_slice_len_eq` before and after the
call, so this is a missing convenience rather than missing information. It is part of the developer's
contract and costs implementations nothing: the crate's three implementations prove it without new proof
steps. **Fix:** `final(dst)@.len() == old(dst)@.len()` added to `TryRng::try_fill_bytes` and
`Rng::fill_bytes` ([`src/lib.rs`](src/lib.rs)).

### C2. `reconstruct`'s precondition is too strong, and Claude's report misstates upstream (fixed)

Claude requires `0 < N <= W::MAX`, and its `VERIFICATION.md` justifies this: "`new`/`reconstruct` require
`0 < N <= W::MAX` (upstream panics for `N == 0`, and for `u32` words with `N > u32::MAX`)". For `reconstruct`
this is wrong. Upstream converts the index with `W::from_usize` only when it builds a result
(`remaining_results.len() < N`); otherwise it returns `None`. Run against upstream,
`reconstruct` with `N == 0` returns `None`, and so does any call with `remaining_results.len() >= N`. The
developer's precondition, `remaining_results.len() < N ==> W::try_from_spec(N).is_ok()`, is the right one.
A call that is valid upstream (`gap_reconstruct_empty_block`) fails against `verus/`. **Fix:** the
developer's precondition; the body verifies unchanged.

### C3. `reset_and_skip` requires a well-formed `BlockRng`, which it does not need (fixed)

`reset_and_skip` never reads the old index: it sets it (`n == 0`) or regenerates the block and sets it.
Claude still requires `old(self).wf()`. This matters because `wf()` is `closed`, so a verified client can
only get it from `new`, `reconstruct` or a method. A `BlockRng` from the derived `Clone`, which has no
contract (Claude's `VERIFICATION.md` lists this under Limitations), can therefore never be used again by
verified code. The developer requires only `N > 0`, `N` fits in `W` and `n < N`. With that precondition and
Claude's postcondition `final(self).wf()`, `reset_and_skip` turns any `BlockRng` into a well-formed one:
`gap_reset_clone` clones a `BlockRng`, resets the clone and calls `next_word` on it. That verifies against the
fixed crate and fails against `verus/`. **Fix:** the developer's precondition.

### C4. `UnwrapErr::re` has no contract (fixed)

The developer's contract (`&*result.0 === &*old(self).0` and `&*final(result.0) === &*final(self).0`: the
result is a reborrow of the same generator) verifies with the body unchanged. Without it, a caller knows
nothing about the generator it gets (`gap_re` fails against `verus/`). **Fix:** the developer's contract
([`src/unwrap_err.rs`](src/unwrap_err.rs)).

### C5. Frame conditions on the output buffer are missing (fixed)

Claude describes a `BlockRng` through `buffer()`, the words not yet consumed. That is the right abstraction
for the words the methods return, but it says nothing about the other words of the buffer, so the contracts
allow a method to overwrite them. The developer's contracts expose the buffer (`spec_results()`) and state
that the other words are unchanged: `next_word`, `next_u64_from_u32` with two words left, `fill_bytes` within
the buffer, and `reset_and_skip(0)`. They also state that `fill_bytes` with an empty `dest` leaves the whole
state unchanged, and that after a refill `next_u64_from_u32` returns `results[1]` in the high half.

The consumed words are not returned by any method, but they are not invisible: `Generator::drop`
receives the whole buffer when the `BlockRng` is dropped (for example, to zero it), and the derived `Clone`
copies it. Mutants M24–M27 overwrite consumed words or leave a different state after an empty `fill_bytes`,
and Claude's crate verifies each of them. **Fix:** the developer's clauses, stated on Claude's functions and
proved. For `fill_bytes` this needed one more conjunct in Claude's loop invariant `inv_fill` ("until a block
is generated, the buffer is the old one") and a lemma, `lemma_fill_bytes_human`. The lemma derives the
developer's two index formulas (`i + ceil(len / size)` when the buffer suffices,
`((words - 1) % N) + 1` after refills) from Claude's `consumes`.

### C6. `fill_bytes_via_next_word` allows an error for an empty `dst` (fixed)

Claude's error case says only that `next_word` may return the error. That holds even when `next_word` is
never called, so the contract allows an implementation that calls `next_word` for an empty `dst` and returns
its error: mutant M23 does this and verifies on Claude's crate. The developer states that an empty `dst`
gives `Ok` and is left unchanged. **Fix:** both clauses added; the body verifies unchanged.

### C7. Inaccurate statements in Claude's `VERIFICATION.md` (fixed in this folder's copy)

- "upstream panics for `N == 0`" for `reconstruct`: false (C2).
- "`seed_from_u64` is proved ... to fill the seed with the PCG32 output stream". The proof is about the slice
  that `seed.as_mut()` returns. For a generic `Seed`, `AsMut::as_mut` has no contract (trusted item S4), so
  nothing connects that slice to the value passed to `from_seed`. It is proved for the bytes written through
  `as_mut`, which is what upstream does.

### Checked and correct

- **No false statement.** Claude's contracts verify, and its 22 negative controls are still rejected, on
  the fixed crate too. Apart from the gaps above, what the developer states follows from Claude's contracts:
  the developer's index and result clauses of `next_word`, `next_u64_from_u32` and `fill_bytes` follow from
  Claude's `consumes` (proved in the fixed crate), and `read_words`'s two postconditions are equivalent.
- **The `unwraps_to` construction of `Rng`.** Claude says that Verus does not know that `Infallible` has no
  values. Confirmed: `proof fn f(r: Result<u32, Infallible>) ensures r is Ok {}` fails.
- **The bug Claude found** (`next_u64_from_u32` panics on every call when `N == 1`) is real (reproduced
  against upstream). Both specs require `N >= 2`.
- **Claude's code changes preserve upstream's behaviour**, with one qualification. A differential test
  ([`verification/differential/run.sh`](verification/differential/run.sh)) runs upstream and this crate
  side by side on every changed function: 421,617 comparisons in a debug build and 421,017 in release,
  panics included, all equal but one. After a caught panic between `generate` and `set_index` (as
  `next_u64_from_u32` with `N == 1` does on every call), the stored index is a generated word, and a
  `fill_bytes(&mut [])` then trips upstream's `debug_assert!` in `set_index`, which Claude removed
  (its condition is proved for every state the API produces). Debug builds only.

## Findings in the developer's spec

Each of H1–H5 is reproduced by Verus:
[`verification/developer_spec_findings.py`](verification/developer_spec_findings.py) runs the experiments
and checks the expected failure of each. The placeholder bodies (`assume(false)` 20 times,
`external_body` 20 times, `external` twice) are expected in a file that states specifications without
proofs, so they are not counted. Neither are the private
helpers that have no contract (`index`, `set_index`, `from_usize`, `into_usize`, `panic_msg`).

| # | Item | Problem |
|---|---|---|
| H1 | `new`, `reconstruct`, `reset_and_skip` vs. `next_word`, `next_u64_from_u32`, `fill_bytes`, `remaining_results` | **The contracts do not compose.** The latter require the index stored in `results[0]` to be in `1..=N`. Nothing ensures it: `new` and `reconstruct` ensure only the core, and `reset_and_skip` says nothing about the index. A client of the developer's crate cannot call `next_word` on `BlockRng::new(..)`, nor `remaining_results` on the result of `reconstruct` ("precondition not satisfied"). The methods re-establish the index (`next_word`, `next_u64_from_u32`, `fill_bytes`), but no method can be called first. The fixed crate ensures Claude's `wf()`, and `lemma_wf_human` proves it equivalent to the developer's precondition |
| H2 | `read_words` | **The precondition cannot be established.** `src@.len() == vstd::layout::size_of::<[W; N]>()` is upstream's assertion, but vstd says nothing about the size of an array: `size_of::<[u32; 2]>() == 8` is not provable. No caller can meet it, not even with concrete types. Claude's `N * size_of::<W>()` is kept |
| H3 | `fill_bytes_via_next_word` | **Missing precondition.** Nothing says that `next_word` may be called. With the developer's contract, Verus rejects both calls in the body ("fails to satisfy `callee.requires(args)`"). As an `external_body` contract it would let a verified caller pass a closure whose precondition does not hold, breaking the closure's own guarantees. Claude's precondition is kept |
| H4 | `word_offset` | **Insufficient precondition.** `N > 0` does not rule out the `unwrap` in `into_usize` (`u64` to `usize`) failing on a target with a 32-bit `usize`, for an index of `2^32` or more. Verus rejects `index()` under it. The public API never produces such an index, but the contract admits it. Fixed: `wf()`, or the index in `1..=N` (the developer's precondition of `remaining_results`) |
| H5 | `next_word`, `fill_bytes` (postconditions) | **Matching loop.** The quantified clauses are triggered on `W::try_from_spec(i as usize)` and conclude `W::try_from_spec((i + 1) as usize) === ...` (or `i + k`, `new_index`), which triggers the same clause again, without end. A client of the developer's crate that calls `next_word` once and then asserts `false` exhausts the solver's resource limit instead of failing; with Claude's crate the same client fails at once. Stated as written in the fixed crate, the clauses made Claude's verified client run out of resources even at 8 times the limit. The fixed crate writes `W::try_from_spec(i as usize) === Ok(x)` as `index_is(x, i)`, an open spec function defined as exactly that, and triggers on `index_is(old(self).spec_results()@[0], i)`. A clause then produces terms about the *new* state only, which chain into the next call instead of looping. The formulas are unchanged; only the triggers differ |
| H6 | `fill_bytes`, `next_word`, `next_u64_from_u32`, `reset_and_skip`, `Rng`/`TryRng` | (weak, not wrong) `Generator::generate` ensures `true`, so nothing can be said about generated words. `fill_bytes` says nothing about the bytes it writes, `next_word` does not say what it returns after a refill, `reset_and_skip` says nothing for `n > 0`, and the `Rng`/`TryRng` methods ensure `true` |

Positive: the developer's frame clauses (C5), the empty-`dst` clauses (C6), the length clause (C1) and the
`re` contract (C4) are all true, and none of them is in Claude's spec. The developer's preconditions of
`reconstruct` and `reset_and_skip` are more precise than Claude's (C2, C3).

## The fixed crate

- **Developer's clauses** are stated on Claude's functions, marked `// Human spec`, and proved. Where one of
  them follows from Claude's, a comment says so instead of repeating it. Postconditions are verbatim, except
  that `W::try_from_spec(i as usize) === Ok(x)` is written `index_is(x, i)` (H5). Preconditions are the
  developer's verbatim where they are kept (`reconstruct`, `reset_and_skip`). `word_offset` and
  `remaining_results` take `self.wf() || (N > 0 && the index is in 1..=N)`, the second being the
  developer's precondition of `remaining_results`. `wf()` implies it (`lemma_wf_human`), but listing `wf()`
  lets callers that know it call these methods without a lemma.
- **New ghost items** (erased from normal builds): `BlockRng::spec_results` (the developer's) and
  `lemma_wf_human` in [`src/block.rs`](src/block.rs); `index_is`; `Word::spec_from_le_bytes` (the
  developer's definitions, verbatim) with `lemma_spec_from_le_bytes` in [`src/word.rs`](src/word.rs);
  `Sealed::lemma_value_injective` and `lemma_try_from_usize`; the broadcast lemma
  `lemma_try_from_usize_spec`, used by `block.rs` at module level, so that no exec function gains a `proof`
  block. Their proofs are verified.
- **Trusted base:** one addition, **S7** in [`src/trusted.rs`](src/trusted.rs). The developer defines
  `u32::spec_from_le_bytes` as vstd's `spec_u32_from_le_bytes`, which vstd declares `closed`. Outside vstd
  nothing can relate it to Claude's encoding (vstd exports the `u64` counterpart, so `u64` needs nothing).
  S7 states vstd's definition verbatim, and `check_trusted.py` compares it with vstd's source text. The
  developer's `TryFromSpec` needs a Verus-only import (`#[cfg(verus_keep_ghost)]`) in `block.rs` and
  `word.rs`. `check_trusted.py` allows that attribute only directly on that import.
- **Tooling** ([`verification/`](verification/)): `verify.sh` also verifies `human_spec_client.rs`,
  `claude_spec_client.rs` and `gap_clients.rs`. `negative_controls.py` has M23–M27, and `--first-pass`
  checks that Claude's crate accepts them and rejects the calls of `gap_clients.rs`. `check_trusted.py`
  checks S7 against vstd and the ghost-only imports. `developer_spec_findings.py` reproduces H1–H5.

## Results (fixed crate)

| | |
|---|---|
| Verus, crate | **129 verified, 0 errors** (Claude's: 105); only the `unreachable call` warning that Claude's crate also has |
| Verified clients | `client_examples.rs` 19, `human_spec_client.rs` 15, `claude_spec_client.rs` 12, `gap_clients.rs` 8; all 0 errors |
| Proof stability | crate and all four clients verify with SMT seeds 0–24 and 77 |
| Negative controls | **27/27 rejected** (Claude's 22 and M23–M27), each with a definite error. (M4's first error is the resource limit, but it also fails an assertion under every seed tried, and with `--rlimit 30` the assertion is its only error. On `verus/`, M5's first error is the resource limit) |
| Gaps of the first pass (`--first-pass`) | M23–M27 all verify on `verus/`; the 4 calls of `gap_clients.rs` all fail against it |
| Findings in the developer's spec | H1–H5 all reproduced (`developer_spec_findings.py`) |
| `check_trusted.py` | 0 failures (C1–C5 upstream code, S7 = vstd's definition, the only `verus_keep_ghost`s are the allowed ones) |
| Normal build | upstream's tests pass (11 integration, 4 doc); `clippy -D warnings`, `rustdoc -D warnings`, `rustfmt --check` clean |
| Differential test | this crate vs upstream on every changed function: 421,617 comparisons (debug) and 421,017 (release), all equal except the debug-only `set_index` case above |
| Executable code | macro-expanded normal build identical to `verus/`'s except comments and one `const _: () = ();` |

## How the specs were compared

1. Both specs were read against upstream [`../src/`](../src/) and its documentation, function by function.
2. Every disagreement was turned into a Verus experiment: a valid call that one contract rejects, a mutant
   that one contract accepts, or a body that one contract cannot prove. The ones that show a gap in Claude's
   spec are kept in `verification/` (`gap_clients.rs`, M23–M27), and so are those about the developer's
   spec (`developer_spec_findings.py`). Runtime claims about upstream
   (`reconstruct` with `N == 0`, `next_u64_from_u32` with `N == 1`) were checked by running upstream.
3. The developer's clauses were added to Claude's functions and proved, and the developer's preconditions
   adopted where they are weaker and sufficient.
4. The developer's contracts, and Claude's, were then restated verbatim in two verified clients that call the
   fixed crate. That both verify is the evidence that the fixed contracts refine both specs, except where
   the developer's precondition is wrong (H2–H4).

## Reproduce

```sh
VERUS=/path/to/verus verus_fixed/verification/verify.sh                          # crate, then 4 clients
VERUS=/path/to/verus python3 verus_fixed/verification/negative_controls.py       # 27 mutants rejected
VERUS=/path/to/verus python3 verus_fixed/verification/negative_controls.py --first-pass   # gaps of verus/
VERUS=/path/to/verus python3 verus_fixed/verification/developer_spec_findings.py        # H1-H5
verus_fixed/verification/differential/run.sh                                            # vs upstream
python3 verus_fixed/verification/check_trusted.py
(cd verus_fixed && cargo test)
```
