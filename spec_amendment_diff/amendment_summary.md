# Notable amendments to Claude's specification of `rand_core`

Claude's first-pass Verus specification ([`verus/`](../verus/src/)) was checked against a developer's
hand-written specification ([`verus_human_written_spec/`](../verus_human_written_spec/src/)), and
amended into [`verus_fixed/`](../verus_fixed/src/). This page picks out the amendments worth noting. The
complete record is [`spec_diff_report.md`](spec_diff_report.md) (every changed item) and
[`spec_diff.diff`](spec_diff.diff) (the diff of the specification: `requires`/`ensures` clauses and the
spec functions they use). Finding ids (C1–C7 for Claude's spec, H1–H6 for the developer's) refer to
[`verus_fixed/SPEC_REVIEW.md`](../verus_fixed/SPEC_REVIEW.md).

## In short

- **No clause of Claude's first pass was false.** What the developer's spec exposed were **gaps**:
  11 clauses that give callers guarantees Claude's contracts lacked. It also exposed **two
  preconditions that rejected valid calls**.
- **15 more of the developer's clauses were added but bring nothing new.** They follow from Claude's
  contracts, and are stated so that the two specifications visibly agree.
- **The developer's spec had defects of its own** (H1–H5). Where it is wrong, the amendment departs from
  it.
- **The cost is all ghost code.** The specification diff is +109 / −5 lines. Outside it there are 76
  lines of lemma statements, 193 lines of proof and one new trusted axiom. **No executable line
  changed.**

| # | Amendment | Functions | Kind | Shown by |
|---|---|---|---|---|
| [1](#1-words-already-consumed-stay-unchanged) | Words already consumed stay unchanged | `next_word`, `next_u64_from_u32`, `fill_bytes`, `reset_and_skip` | gap (C5) | mutants M24, M26 |
| [2](#2-an-empty-fill_bytes-leaves-the-state-unchanged) | An empty `fill_bytes` leaves the state unchanged | `BlockRng::fill_bytes` | gap (C5) | mutant M25 |
| [3](#3-the-high-half-of-next_u64_from_u32-after-a-refill) | The high half of `next_u64_from_u32` after a refill | `next_u64_from_u32` | gap (C5) | mutant M27 |
| [4](#4-unwraperrre-gets-a-contract) | `UnwrapErr::re` gets a contract | `UnwrapErr::re` | gap (C4) | client `gap_re` |
| [5](#5-an-empty-dst-gives-ok) | An empty `dst` gives `Ok` | `fill_bytes_via_next_word` | gap (C6) | mutant M23 |
| [6](#6-dst-keeps-its-length) | `dst` keeps its length | `TryRng::try_fill_bytes`, `Rng::fill_bytes` | gap (C1) | client `gap_fill_bytes_len` |
| [7](#7-reconstruct) | Weaker precondition | `reconstruct` | precondition (C2) | client `gap_reconstruct_empty_block` |
| [8](#8-reset_and_skip) | Weaker precondition | `reset_and_skip` | precondition (C3) | client `gap_reset_clone` |
| [9](#9-index_is-instead-of-the-developers-triggers-h5) | `index_is` instead of the developer's triggers | `next_word`, `fill_bytes` | developer's defect (H5) | `developer_spec_findings.py` |
| [10](#10-developers-preconditions-that-were-not-adopted-h1-h2-h4) | Developer's preconditions not adopted | `word_offset`, `read_words`, `next_word`, … | developer's defect (H1, H2, H4) | `developer_spec_findings.py` |

Mutants M23–M27 ([`negative_controls.py`](../verus_fixed/verification/negative_controls.py#L118-L174))
change the code in ways that only the developer's clauses rule out. Each verifies against Claude's
first pass and is rejected by the amended crate. The clients in
[`gap_clients.rs`](../verus_fixed/verification/gap_clients.rs) are valid calls that fail against the first
pass and verify against the amended crate.

## New guarantees

### 1. Words already consumed stay unchanged

Claude described a `BlockRng` through `buffer()`, the words not yet consumed, and `consumes(..)`, the
words returned. That says nothing about the words already consumed (`results[1..index]`), so the
contracts allowed a method to overwrite them. Those words are observable: `Generator::drop` receives the
whole buffer (for example, to zero it), and the derived `Clone` copies it. The developer's spec states
that the other words of the buffer are unchanged, and the amendment adds this to four methods.

Claude's `next_word` ([verus/src/block.rs:364-369](../verus/src/block.rs#L364-L369)):

```rust
    pub fn next_word(&mut self) -> (r: W)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).consumes(final(self), 1, seq![r]),
```

The developer's clause, added ([verus_fixed/src/block.rs:474-487](../verus_fixed/src/block.rs#L474-L487);
the developer's original is at [verus_human_written_spec/src/block.rs:311-329](../verus_human_written_spec/src/block.rs#L311-L329)):

```rust
            forall|i: int|
                0 <= i < N as int && #[trigger] index_is(old(self).spec_results()@[0], i) ==> {
                    // ...
                    // other buffered words remain unchanged
                    &&& forall|j: int|
                        1 <= j < N as int ==> final(self).spec_results()@[j] == old(
                            self,
                        ).spec_results()@[j]
                },
```

The same frame condition was added to:
- `next_u64_from_u32` with two words left: [verus_fixed/src/block.rs:553-554](../verus_fixed/src/block.rs#L553-L554).
- `fill_bytes` when the buffer covers `dest`: [verus_fixed/src/block.rs:640-657](../verus_fixed/src/block.rs#L640-L657).
- `reset_and_skip(0)`: [verus_fixed/src/block.rs:391-392](../verus_fixed/src/block.rs#L391-L392).

```rust
            n == 0 ==> forall|i: int|
                1 <= i < N as int ==> final(self).spec_results()@[i] == old(self).spec_results()@[i],
```

Most of the amendment's proof work went into `fill_bytes`. Claude's loop invariant
[`inv_fill`](../verus_fixed/src/block.rs#L875) gained one conjunct (until a block is generated, the
buffer is the old one), and a 95-line lemma,
[`lemma_fill_bytes_human`](../verus_fixed/src/block.rs#L1037), proves the developer's four clauses of
`fill_bytes`.

### 2. An empty `fill_bytes` leaves the state unchanged

Claude's `fill_bytes` says that no word is consumed when `dest` is empty, but because of the gap in 1 it
allowed the consumed words to change. The developer's clause rules this out
([verus_fixed/src/block.rs:635](../verus_fixed/src/block.rs#L635); developer's:
[verus_human_written_spec/src/block.rs:436-437](../verus_human_written_spec/src/block.rs#L436-L437)):

```rust
            old(dest)@.len() == 0 ==> *final(self) === *old(self),
```

Mutant M25 ([negative_controls.py:138](../verus_fixed/verification/negative_controls.py#L138)) overwrites
a consumed word on an empty `fill_bytes`. It verifies against the first pass.

### 3. The high half of `next_u64_from_u32` after a refill

When the buffer is exhausted, `next_u64_from_u32` generates a block and uses its first words. Claude's
contract describes the result through the words consumed, but not where they sit in the new buffer. The
developer pins the high half to `results[1]`
([verus_fixed/src/block.rs:567-568](../verus_fixed/src/block.rs#L567-L568); developer's:
[verus_human_written_spec/src/block.rs:389-391](../verus_human_written_spec/src/block.rs#L389-L391)):

```rust
            (old(self).spec_results()@[0] as usize) >= N
                ==> (r >> 32) == final(self).spec_results()@[1] as u64,
```

Mutant M27 ([negative_controls.py:165](../verus_fixed/verification/negative_controls.py#L165)) zeroes the
word it used as the high half. It verifies against the first pass.

### 4. `UnwrapErr::re` gets a contract

Claude's `re` had no contract, so a caller knew nothing about the generator it got back
([verus/src/unwrap_err.rs:89-94](../verus/src/unwrap_err.rs#L89-L94)). The developer's contract was
adopted verbatim, and the body verifies unchanged
([verus_fixed/src/unwrap_err.rs:89-96](../verus_fixed/src/unwrap_err.rs#L89-L96); developer's:
[verus_human_written_spec/src/unwrap_err.rs:72-77](../verus_human_written_spec/src/unwrap_err.rs#L72-L77)):

```diff
-    pub fn re<'b>(&'b mut self) -> UnwrapErr<&'b mut R>
+    pub fn re<'b>(&'b mut self) -> (result: UnwrapErr<&'b mut R>)
     where
         'r: 'b,
+        ensures
+            &*result.0 === &*old(self).0,
+            &*final(result.0) === &*final(self).0,
```

The result reborrows the same generator: it starts in the generator's current state, and the
generator ends in the state the result leaves. Client:
[`gap_re`](../verus_fixed/verification/gap_clients.rs#L40-L45).

### 5. An empty `dst` gives `Ok`

Claude's error case for `fill_bytes_via_next_word` only says that `next_word` returned the error. That
holds even if `next_word` is called needlessly, so the contract allowed an implementation that calls
`next_word` for an empty `dst` and fails. The developer's first clause rules this out; the second already
follows from Claude's length clause
([verus_fixed/src/utils.rs:238-239](../verus_fixed/src/utils.rs#L238-L239); developer's:
[verus_human_written_spec/src/utils.rs:124-125](../verus_human_written_spec/src/utils.rs#L124-L125)):

```rust
        old(dst)@.len() == 0 ==> res.is_ok(),
        old(dst)@.len() == 0 ==> final(dst)@ === old(dst)@,
```

Mutant M23 ([negative_controls.py:120](../verus_fixed/verification/negative_controls.py#L120)) does
exactly that. It verifies against the first pass.

### 6. `dst` keeps its length

Claude's `try_fill_bytes` and `fill_bytes` contracts are the implementation's hook, which need not
mention lengths. After `rng.fill_bytes(buf)`, a caller could not prove `buf`'s length without calling
vstd's `mut_ref_slice_len_eq`. This is a convenience rather than missing information. The developer's
clause was added to both trait methods
([verus_fixed/src/lib.rs:103](../verus_fixed/src/lib.rs#L103) and
[verus_fixed/src/lib.rs:270](../verus_fixed/src/lib.rs#L270); developer's:
[lib.rs:104](../verus_human_written_spec/src/lib.rs#L104) and
[lib.rs:251](../verus_human_written_spec/src/lib.rs#L251)):

```rust
            final(dst)@.len() == old(dst)@.len(),
```

Client: [`gap_fill_bytes_len`](../verus_fixed/verification/gap_clients.rs#L31-L38).

## Preconditions that rejected valid calls

### 7. `reconstruct`

Claude required `0 < N <= W::MAX` and justified it in its report: "upstream panics for `N == 0`"
([verus/VERIFICATION.md:189-190](../verus/VERIFICATION.md#L189-L190)). That claim is false. Upstream
builds a result, and so needs `N` to fit in `W`, only when `remaining_results` is shorter than `N`.
Otherwise it returns `None`, including for `N == 0`, which was checked by running upstream. The
developer's precondition is the precise one
([verus_fixed/src/block.rs:191](../verus_fixed/src/block.rs#L191); developer's:
[verus_human_written_spec/src/block.rs:189](../verus_human_written_spec/src/block.rs#L189)):

```diff
         requires
-            0 < N <= W::spec_max(),
+            remaining_results@.len() < N ==> W::try_from_spec(N).is_ok(),
```

Client: [`gap_reconstruct_empty_block`](../verus_fixed/verification/gap_clients.rs#L47-L64). The
false statement is corrected in [`verus_fixed/VERIFICATION.md`](../verus_fixed/VERIFICATION.md) (C7).

### 8. `reset_and_skip`

Claude required `old(self).wf()`, but `reset_and_skip` never reads the old index. Since `wf()` is closed,
a verified client can only get it from `new`, `reconstruct` or another method. A `BlockRng` from the
derived `Clone`, which has no contract, could therefore never be used again. With the developer's
precondition, `reset_and_skip` turns any `BlockRng` into a well-formed one
([verus_fixed/src/block.rs:379-381](../verus_fixed/src/block.rs#L379-L381); developer's:
[verus_human_written_spec/src/block.rs:241-244](../verus_human_written_spec/src/block.rs#L241-L244)):

```diff
         requires
-            old(self).wf(),
+            N > 0,
+            W::try_from_spec(N).is_ok(),
             n < N,
```

Client: [`gap_reset_clone`](../verus_fixed/verification/gap_clients.rs#L66-L75) clones a `BlockRng`,
resets the clone and calls `next_word` on it.

`remaining_results` and `word_offset` also accept the developer's form of the precondition, an index
in `1..=N` ([verus_fixed/src/block.rs:450-453](../verus_fixed/src/block.rs#L450-L453)). This is
weaker than `wf()` only by `N <= W::MAX`, which these methods don't need. The difference is marginal,
because every `BlockRng` the API builds is `wf()`.

## Where the developer's spec was not followed

### 9. `index_is` instead of the developer's triggers (H5)

The developer's quantified postconditions of `next_word` and `fill_bytes` are triggered on
`W::try_from_spec(i as usize)`, and conclude a new term of the same form
([verus_human_written_spec/src/block.rs:311-324](../verus_human_written_spec/src/block.rs#L311-L324)):

```rust
            forall|i: int|
                0 <= i < N as int &&
                #[trigger] W::try_from_spec(i as usize) === Ok(old(self).spec_results()@[0])
                ==>
                {
                    // ...
                    &&& W::try_from_spec((i + 1) as usize)
                        === Ok(final(self).spec_results()@[0])
```

Each conclusion triggers the clause again, without end: a matching loop. A client that calls
`next_word` once exhausts the solver. The amendment keeps the formulas but writes the predicate as an
open spec function ([verus_fixed/src/block.rs:96-98](../verus_fixed/src/block.rs#L96-L98)):

```rust
pub open spec fn index_is<W: Word>(x: W, i: int) -> bool {
    W::try_from_spec(i as usize) === Ok(x)
}
```

It then triggers on `index_is(old(self).spec_results()@[0], i)`, so that a clause produces terms about
the new state only (amended `next_word`:
[verus_fixed/src/block.rs:474-492](../verus_fixed/src/block.rs#L474-L492)). This substitution is the
main textual difference between the developer's clauses and the amended crate's: the developer's
clauses of `reconstruct`, `reset_and_skip`, `next_u64_from_u32`, `re` and `fill_bytes_via_next_word`
are copied as written.

### 10. Developer's preconditions that were not adopted (H1, H2, H4)

- **`word_offset` (H4).** The developer requires only `N > 0`. That does not rule out an index of
  2^32 or more, for which `into_usize` panics on a target with 32-bit `usize`, and Verus rejects the
  body under it. The amendment requires `wf()` or an index in `1..=N`
  ([verus_fixed/src/block.rs:419-422](../verus_fixed/src/block.rs#L419-L422)).
- **`read_words` (H2).** The developer's `src@.len() == vstd::layout::size_of::<[W; N]>()`
  ([verus_human_written_spec/src/utils.rs:164](../verus_human_written_spec/src/utils.rs#L164)) cannot
  be established by any caller: vstd says nothing about the size of an array. Claude's
  `N * size_of::<W>()` is kept. The developer's postconditions were added
  ([verus_fixed/src/utils.rs:356-363](../verus_fixed/src/utils.rs#L356-L363)).
- **`next_word`, `next_u64_from_u32`, `fill_bytes` (H1).** The developer's preconditions are
  equivalent to Claude's closed `wf()`, as proved by
  [`lemma_wf_human`](../verus_fixed/src/block.rs#L293). Claude's are kept because they compose: `new`
  ensures `wf()`. The developer's `new` and `reconstruct` ensure only the core, so no client of the
  developer's spec can call `next_word` on a new `BlockRng`.
- **`fill_bytes_via_next_word` (H3).** The developer's contract has no precondition, so `next_word`
  might not be callable. Claude's `forall|| next_word.requires(())` is kept.

## Restatements

15 of the added clauses already follow from Claude's `consumes`-based contracts, and are proved. Some
examples:
- `reconstruct` returns `None` iff `remaining_results` is too long
  ([block.rs:197](../verus_fixed/src/block.rs#L197)).
- Six of `next_u64_from_u32`'s eight case clauses
  ([block.rs:549-570](../verus_fixed/src/block.rs#L549-L570)).
- The developer's index formulas for `fill_bytes`
  ([block.rs:659-672](../verus_fixed/src/block.rs#L659-L672)).
- `read_words`'s word-by-word decoding ([utils.rs:357-363](../verus_fixed/src/utils.rs#L357-L363)).

They give callers nothing new, but they document that the developer's view and Claude's agree.

## What it cost

| | Lines | Where |
|---|---|---|
| New spec functions: the developer's vocabulary | +13 (in the spec diff) | [`spec_results`](../verus_fixed/src/block.rs#L248), [`index_is`](../verus_fixed/src/block.rs#L96), `spec_from_le_bytes` ([trait](../verus_fixed/src/word.rs#L10), [u32](../verus_fixed/src/word.rs#L33), [u64](../verus_fixed/src/word.rs#L56)) |
| Lemmas relating the two vocabularies (statements) | +76 | e.g. [`lemma_wf_human`](../verus_fixed/src/block.rs#L293), `lemma_try_from_usize`, `lemma_spec_from_le_bytes` in [word.rs](../verus_fixed/src/word.rs) |
| Proof | +193 −2 | 95 of them in [`lemma_fill_bytes_human`](../verus_fixed/src/block.rs#L1037) |
| Trusted base | one axiom | [S7](../verus_fixed/src/trusted.rs#L229) restates vstd's closed `spec_u32_from_le_bytes`, needed only for the developer's `spec_from_le_bytes` on `u32` |
| Executable code | 0 | — |

Counts are from [`spec_diff_report.md`](spec_diff_report.md#summary).
