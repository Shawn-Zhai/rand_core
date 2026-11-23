# Verifying `rand_core` with Verus

Crate: `rand_core` 0.10.1 (`master` @ fdea405). Verus 0.2026.11.22.1ce6a59 with its bundled vstd;
the normal build uses rustc 1.100.0 and the `vstd` crate 0.0.0-2026-11-22-0344. The annotated
crate is this folder (`verus/`); upstream is `../src`. Specifications and proofs written by Claude
(Opus 5.5) in Claude Code, 2026-11-18, from the crate's documentation, tests and code, with
Verus 0.2026.05.03.8b81855; ported to 0.2026.11.22.1ce6a59 on 2026-11-23 (see
[Port to Verus 0.2026.11.22](#port-to-verus-020261122)).

## Summary

| | |
|---|---|
| Verus | **105 verified, 0 errors** (about 2 s), default resource limits |
| Verified client of the specifications | **19 verified, 0 errors** ([`verification/client_examples.rs`](verification/client_examples.rs)) |
| `assume`, `admit`, axioms, `external_body`, `assume_specification` outside `src/trusted.rs` | **none**; no code outside `verus!` either ([`check_trusted.py`](verification/check_trusted.py)) |
| Trusted base ([`src/trusted.rs`](src/trusted.rs)) | 3 specifications of std items (S1, S3, S4; S2, S5, S6 are now vstd's), 5 pieces of code (C1-C5): the `Debug` impl and `panic_msg` (upstream, verbatim), the bodies of upstream's two `assert`s, and 4 one-line wrappers of `{to,from}_le_bytes` |
| Negative controls | **22/22** injected bugs rejected ([`negative_controls.py`](verification/negative_controls.py)), including a wrong *trusted* specification (M22) and a code-and-spec change that only the PCG32 test vector catches (M21) |
| Differential test (annotated vs upstream, normal build) | 31,350 comparisons equal, debug and release, panics and their messages included (run before the port, with rustc 1.95; the port changed no executable code) |
| Proof stability | verifies with SMT seeds 1-24 (crate), 0, 5, 77 (crate and client) |
| Normal build | builds; upstream's tests pass (11 integration, 4 doc tests); `clippy -D warnings`, `rustdoc -D warnings`, `rustfmt --check` clean |
| Code changes | 40 findings of `code_change_detection/detect_changes.py`, each explained in `code_change_detection/approved_changes.json` (`agent_note`), **awaiting human review**. After the port, 5 findings have new fingerprints and 2 entries (S5, S6) match nothing; `approved_changes.json` has not been updated for that (see the port section) |
| Bug found | `BlockRng::next_u64_from_u32` panics (index out of bounds) on every call when the block has one word (`N == 1`) |

## Reproduce

```sh
VERUS=/path/to/verus verus/verification/verify.sh          # crate, then the verified client
VERUS=/path/to/verus python3 verus/verification/negative_controls.py
python3 verus/verification/check_trusted.py
(cd verus && cargo test)                                    # upstream's tests, normal build
python3 code_change_detection/detect_changes.py src/ verus/ # exits 1 until the changes are reviewed
```

`verify.sh` runs `verus --crate-type=lib --edition=2024 src/lib.rs` (exporting the crate's
specifications), then verifies the client against them.

## What is specified and proved

All exec code outside `trusted.rs` is verified: no panics (indexing, arithmetic overflow,
`unwrap`, slicing) under the stated preconditions, termination, and the contracts below.
Upstream's `debug_assert!`s are proved instead of checked (they are removed, see "Changes").

### `utils` and the `Word` trait

`le_bytes(w)` is the little-endian encoding of a word (`w.to_le_bytes()`), `le_bytes_of_words(ws)`
the concatenation over `ws`. `lemma_le_bytes_u32` / `_u64` state the bytes explicitly.

| Item | Contract |
|---|---|
| `read_words::<W, N>(src)` | requires `src.len() == N * size_of::<W>()` (upstream's `assert_eq!`, which panics otherwise). Returns `r` with `le_bytes_of_words(r) == src` |
| `fill_bytes_via_next_word(dst, next_word)` | `dst` keeps its length. On `Ok`: `dst == le_bytes_of_words(words)[..dst.len()]` where every word is a value `next_word` may return (`next_word.ensures((), Ok(w))`), and `words` is the fewest that cover `dst` (`ceil(len / size)` calls). On `Err(e)`: `next_word` returned `Err(e)` |
| `next_word_via_fill(rng)` | on `Ok(w)`: one `try_fill_bytes` call on a `size_of::<W>()`-byte buffer, and the bytes it wrote are `le_bytes(w)`. On `Err(e)`: that call returned `Err(e)` |
| `next_u64_via_u32(rng)` | on `Ok(v)`: two successive `try_next_u32` results `x`, `y` (through an intermediate state) with `v == (y << 32) \| x`. On `Err(e)`: the first call failed, or the first succeeded and the second failed with `e` |
| `Word::{from,to}_le_bytes`, `from_usize`, `into_usize` | little-endian conversion (round trip proved by bit-vector); `from_usize`/`into_usize` require the value to fit (upstream `unwrap`s) and preserve it |

### `TryRng`, `Rng`, `UnwrapErr`

`TryRng` gets three specification hooks that each implementation defines:
`try_next_u32_post(pre, post, res)`, `try_next_u64_post`, `try_fill_bytes_post(pre, post, dst_pre,
dst_post, res)`; each method ensures its hook. A downstream implementation states what its
generator does; one that does not care defines `true`.

| Item | Contract |
|---|---|
| `Rng::next_u32` / `next_u64` / `fill_bytes` (blanket impl over `TryRng<Error = Infallible>`) | the result is the `Ok` value of a possible `try_*` result. (Verus treats `Infallible` as an opaque type, so the contract is stated for a result that is `Ok(r)` *or an error*; with `Infallible` it is always `Ok`. No axiom is used.) |
| `UnwrapErr<R>` | each method returns `Ok` with the wrapped generator's `Ok` value (`map_err(panic_msg)`: `panic_msg` never returns) |
| `impl<R: DerefMut> TryRng for R` | the result is a possible result of the target generator. (`deref_mut` has no contract, so the target's state cannot be related to `self`.) |

### `block`: `Generator` and `BlockRng`

`Generator` gets the hook `generate_post(pre, post, output)`. `BlockRng` has three abstract views:
`wf()` (well-formed: `0 < N <= W::MAX`, the index stored in `results[0]` is in `1..=N`),
`buffer()` (the unconsumed words, in order) and `spec_core()`. The central predicate is
`consumes(self, next, k, words)`: `words` are the next `k` words of the *stream* = the buffer
followed by blocks produced by successive `generate` calls, consumed in order, a block being
generated only when the buffer is exhausted and another word is needed. This is the module
documentation's guarantee ("All values are consumed in-order of generation. No whole words are
discarded").

| Item | Contract |
|---|---|
| `new(core)` | requires `0 < N <= W::MAX`; `wf`, empty buffer, `core` |
| `reconstruct(core, rest)` | requires `0 < N <= W::MAX`; `Some` (well-formed, buffer `rest`) iff `rest.len() < N` |
| `next_word` | `consumes(old, new, 1, [r])` |
| `next_u64_from_u32` (`u32` words) | requires `N >= 2`; `consumes(old, new, 2, [lo, hi])` and `r == hi << 32 \| lo` |
| `fill_bytes(dest)` | `consumes(old, new, k, words)` with `k = ceil(dest.len() / size)` and `dest == le_bytes_of_words(words)[..dest.len()]` (the rest of the last word is discarded) |
| `reset_and_skip(n)` | requires `n < N` (upstream's `assert!`). `n == 0`: empty buffer, core unchanged. `n > 0`: one block generated, buffer = its words `n..` |
| `word_offset` | `0` if the buffer is empty, else `N - buffer.len()`; `< N` |
| `remaining_results` | the buffer; length `< N` |

Every method requires `wf()`; those that take `&mut self` also ensure it.

### `SeedableRng`

The default methods may be overridden by implementations, so the trait gets no contract that
would bind them. Their bodies are verified: `seed_from_u64` is proved (by loop invariant and a
final assertion) to fill the seed with the PCG32 output stream (`pcg32_bytes(state, n)`, `n` the
fewest 4-byte outputs that cover the seed, the last truncated). `pcg32` has a full functional
contract (`pcg32_step`: `state * MUL + INC mod 2^64`; `pcg32_output`: the XSH RR output).
`lemma_pcg32_test_vector` proves that the specification reproduces upstream's value test
(`seed_from_u64(0)` on an 8-byte seed is `5029875928683246316`); since it goes through the
trusted specifications of `rotate_right` (vstd's) and `to_le_bytes`, it also checks those against
a known output.

## Trusted base

All of it is in [`src/trusted.rs`](src/trusted.rs), whose header lists each item and why.

- **S1, S3, S4, specifications of std items** (compiled only under Verus, like vstd's own
  `std_specs`): the traits `core::error::Error`, `AsRef`, `AsMut` (so that Verus accepts them as
  bounds), `as_ref`/`as_mut` on arrays. S2 (`DerefMut`), S5 (`copy_from_slice`) and S6
  (`u32::rotate_right`) are provided by vstd since Verus 0.2026.11.22, with the same contracts.
- **C1** `impl fmt::Debug for BlockRng` and **C2** `panic_msg`: upstream code, verbatim
  (formatting and formatted panics are not supported by Verus). C2's contract is `ensures false`
  (it always panics).
- **C3, C4**: upstream's `assert!(n < N)` (`reset_and_skip`) and
  `assert_eq!(size_of_val(src), size_of::<[W; N]>())` (`read_words`), verbatim, each in an
  `#[inline(always)] #[track_caller]` function whose precondition is the asserted condition.
  Verus does not support panics; this way verified callers must prove the condition, and
  unverified callers get upstream's check with the same message and location. C4 relies on the
  array layout `size_of::<[W; N]>() == N * size_of::<W>()` (Rust Reference), which vstd does not
  state.
- **C5**: `{u32,u64}::{to,from}_le_bytes`, wrapped (`#[inline(always)]`, body = the std call)
  with a little-endian contract; their std signatures (`[u8; size_of::<Self>()]`) cannot take an
  `assume_specification`.

Also trusted: Verus, Z3, rustc, vstd's specifications of the std items used (slice/array
indexing, `split_at_mut`, `copy_from_slice`, `wrapping_*`, `u32::rotate_right`, `DerefMut`,
`TryFrom` between integers, `Result::{unwrap, map_err}`, `?`, `size_of`, closures), and the
`verus!` macro erasing only ghost code.

## Changes to the executable code

`python3 code_change_detection/detect_changes.py src/ verus/` compares the macro-expanded code
(ghost code erased) item by item. Its 40 findings are explained in
`code_change_detection/approved_changes.json` (`agent_note`); `reviewer` is left empty for a
human. In short:

- **Loops over iterators** (`chunks_exact(_mut)`, `zip`, `iter_mut`, `for_each`,
  `into_remainder`; unsupported) rewritten as index loops with the same calls in the same order:
  `fill_bytes_via_next_word`, `read_words`, `BlockRng::fill_bytes`, `SeedableRng::seed_from_u64`.
  `&mut x[a..]` (unsupported) became `split_at_mut`.
- **Slicing** `[..n]` -> `[0..n]` and `results[index..]` -> `results[index..N]` (same slices;
  Verus does not support `RangeTo`/`RangeFrom`).
- **Panics**: the two `assert`s moved verbatim into C3/C4; the two `debug_assert`s
  (`set_index`, `fill_bytes`) removed, their conditions proved.
- **`AsMut` on `W::Bytes`**: Verus cannot specify `AsMut::as_mut` generically (its
  `old`/`final` need `Self: MetaSized`), so the private sealed trait gained
  `bytes_as_mut(bytes) = bytes.as_mut()`, called by `next_word_via_fill` and `read_words`.
- **Moved to `trusted.rs`**: the `Debug` impl (unchanged) and `panic_msg` (now `pub(crate)`);
  calls of `to_le_bytes`/`from_le_bytes` go through the C5 wrappers.
- **Build files**: `vstd` dependency, `rust-version` 1.100, `rust-toolchain.toml`.

Evidence that these changes preserve behaviour: the differential test below; MIR of the release
build is byte-identical whether each module imports `vstd::prelude::*` or only
`vstd::prelude::verus` (so the glob import changes no name resolution); and upstream's tests pass.

## Validation

- **Negative controls** ([`negative_controls.py`](verification/negative_controls.py)): 22 mutants
  (wrong index arithmetic, swapped words, unconsumed partial word, wrong PCG constants, reversed
  words, a big-endian decoder, ...) are all rejected. M22 corrupts the *trusted* `to_le_bytes`
  specification, and M21 makes `pcg32` and its specification both rotate left instead of right
  (consistent with each other); the PCG32 test-vector lemma rejects both. (Before the port, M21
  corrupted this crate's trusted `rotate_right` specification, which vstd now provides.) Two
  mutants (M3, M5) are rejected by the solver's resource limit rather than a definite
  counterexample (with Verus 0.2026.05.03 there were four: M3, M5, M7, M18).
- **Verified client** ([`client_examples.rs`](verification/client_examples.rs)), verified against
  the exported specifications as a downstream crate would be: a counting block generator; on a
  new `BlockRng` the contracts determine that two `next_word`s return 10 and 11, a 6-byte
  `fill_bytes` writes `[12, 0, 0, 0, 13, 0]` without generating, and `next_u64_from_u32` then
  generates the next block and returns `0xf_0000_000e`; `read_words` decodes concrete bytes;
  `UnwrapErr` and `next_u64_via_u32` results are determined.
- **Differential test** (scratch harness, not part of the crate): upstream and the annotated crate
  side by side on random operation sequences on `BlockRng` (N = 1, 2, 3, 4, 16 for `u32`;
  1, 5, 8 for `u64`), `fill_bytes_via_next_word` with errors at every call, `read_words` at every
  offset and length (panics included), `seed_from_u64` for 8 seed lengths and 3000 states,
  fallible generators and `UnwrapErr` panics: 31,350 comparisons, all equal, debug and release.
  The harness detects an injected one-line change.

## Findings

1. **`next_u64_from_u32` with `N == 1`**: the index is always 1, so the `else` branch runs, and
   with `index >= N` it reads `self.results[1]`: index out of bounds on every call. Not
   documented upstream. The verified contract requires `N >= 2`; the differential test shows
   both crates panicking identically.
2. **Documented panics are preconditions**: `reset_and_skip` requires `n < N`; `read_words`
   requires the exact length; `new`/`reconstruct` require `0 < N <= W::MAX` (upstream panics
   for `N == 0`, and for `u32` words with `N > u32::MAX`).

## Limitations

- **`TryRng` contracts are hooks**: the crate cannot know what a generator returns; its contracts
  relate the results of the generic code to the implementation's hooks. For `&mut R`, `Box<R>`
  (the `DerefMut` impl) the hook only says "a possible result of the target".
- **Verus restrictions for downstream verified code**: `BlockRng` is opaque outside `block`
  (it has a private field), so verified clients cannot use the public `core` field; the derived
  `Clone` impls have no contract; a `TryRng` impl cannot call `next_u64_via_u32(self)` from its
  own methods (Verus rejects the cycle through the impl being defined; upstream's tests do this,
  and they are unverified Rust, so they are unaffected).
- `Generator::drop` is declared `opens_invariants none no_unwind` (Verus requires it of `Drop`
  code); verified implementations must not panic in it.
- `SeedableRng`'s default methods have no trait-level contract (see above).
- The trusted base is not proved: it is checked by inspection (`check_trusted.py` compares the
  code with upstream), by the PCG32 test vector and by the differential test.

## Port to Verus 0.2026.11.22

On 2026-11-23 the crate was moved from Verus 0.2026.05.03.8b81855 (rustc 1.95.0) to
0.2026.11.22.1ce6a59 (rustc 1.100.0, Z3 4.16.0). The new release's Z3 needs glibc 2.38 or later
(Ubuntu 24.04).

- **Specifications now in vstd**: the new vstd specifies `u32::rotate_right`, `DerefMut` and
  `copy_from_slice`, which clashed with S6, S2 and S5 ("duplicate specification"). Their contracts
  are the same as ours, so S2, S5 and S6 were removed from `trusted.rs`, and `pcg32_output` uses
  `vstd::wrapping::u32_specs::rotate_right`, which defines the same rotation as the old S6.
- **Build files**: `rust-toolchain.toml` 1.95.0 -> 1.100.0, `rust-version` 1.95 -> 1.100,
  `vstd` 0.0.0-2026-05-06-1803 -> 0.0.0-2026-11-22-0344.
- **Negative control M21** now mutates code and specification together (see Validation), and
  `negative_controls.py` accepts mutations at several sites of one file.
- **No proof changed.** Re-checked after the port: crate 105 verified and client 19 verified,
  0 errors; SMT seeds 1-24 (crate), 0, 5, 77 (crate and client); 22/22 negative controls;
  `check_trusted.py`; upstream's tests; `clippy -D warnings`, `rustdoc -D warnings`,
  `rustfmt --check`.
- **New warning**: Verus builds report "unreachable call" at the `ensures false` of C2
  (`panic_msg`): rustc sees the generated postcondition check after `panic!`. It is harmless; C2
  is left verbatim.
- **Code change detection**: still 40 findings. Under rustc 1.100, `assert_eq!` and
  `debug_assert_eq!` expand with an extra outer block, so the findings for `read_words`,
  `BlockRng::fill_bytes` and `check_read_words_len` have new fingerprints with unchanged code;
  `Cargo.toml` and `rust-toolchain.toml` changed as above; the entries for the removed S5 and S6
  match nothing. `approved_changes.json` still has the pre-port fingerprints and notes for these.
- **Possible follow-up**: vstd now specifies `u32`/`u64::from_le_bytes` (but not `to_le_bytes`),
  so the two `from` wrappers of C5 could be replaced by vstd's specification.
