#!/usr/bin/env python3
"""Checks on the trusted base of the annotated crate. Usage: python3 verus/verification/check_trusted.py

1. Every file other than `src/trusted.rs` is verified code: it contains no construct that makes
   code trusted (`external_body`, `external`, `assume_specification`, `external_fn_specification`,
   `external_trait_specification`, `admit`, `assume`, `axiom`, `uninterp`, `verifier::truncate`,
   `exec_allows_no_decreases_clause`, `assume_termination`, `unsafe`, `verus_keep_ghost`) and no
   code outside `verus!` (only `use`/`mod` declarations, attributes and comments).
2. The code in `src/trusted.rs` is upstream's: C1 and C2 verbatim (C2 up to `pub(crate)` and its
   contract), the statements wrapped by C3 and C4 verbatim, and C5 calls exactly the standard
   library functions that upstream calls.
3. The axiom S7 in `src/trusted.rs` states vstd's definition of `spec_u32_from_le_bytes`
   verbatim (read from vstd's source in the cargo registry, at the version of `Cargo.toml`).
Exits 1 on any failure."""
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(os.path.dirname(HERE), 'src')
UP = os.path.join(os.path.dirname(os.path.dirname(HERE)), 'src')
TRUST = re.compile(r'external_body|verifier::external\b|assume_specification|external_fn_specification|'
                   r'external_trait_specification|\badmit\s*\(|\bassume\s*\(|\baxiom\b|\buninterp\b|'
                   r'verifier::truncate|exec_allows_no_decreases_clause|assume_termination|\bunsafe\b|'
                   r'verus_keep_ghost')

# The one line outside trusted.rs that mentions `verus_keep_ghost`: in Verus builds only, it
# enables the unstable feature that the specifications in trusted.rs (`PointeeSized`) need. It
# changes nothing in a normal build and makes no code trusted.
ALLOWED = {'lib.rs': ['#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]']}
# A `#[cfg(verus_keep_ghost)]` attribute is also allowed on exactly this import, the next line:
# in Verus builds it brings `try_from_spec` (the specification of `TryFrom::try_from`, used by
# the developer's spec) into scope for ghost code; in a normal build the import is absent, and
# the ghost code that uses it is erased. The trait has only spec functions, so the import cannot
# change which exec function a call resolves to.
GHOST_IMPORT = 'use vstd::std_specs::convert::TryFromSpec;'

failures = 0


def fail(msg):
    global failures
    failures += 1
    print('FAIL ' + msg)


def strip_comments(text):
    return re.sub(r'//[^\n]*', '', text)


def strip_attributes(text):
    """Remove `#[...]` and `#![...]` attributes (balanced brackets, possibly multi-line)."""
    out, i = [], 0
    while True:
        m = re.search(r'#!?\[', text[i:])
        if not m:
            out.append(text[i:])
            return ''.join(out)
        out.append(text[i:i + m.start()])
        j, depth = i + m.end(), 1
        while depth:
            depth += {'[': 1, ']': -1}.get(text[j], 0)
            j += 1
        i = j


def outside_verus(text):
    """Top-level text of a file outside `verus! { ... }` blocks (and outside `mod x { ... }`
    bodies, which are checked recursively)."""
    out, i = [], 0
    while True:
        m = re.search(r'verus!\s*\{', text[i:])
        if not m:
            out.append(text[i:])
            break
        out.append(text[i:i + m.start()])
        j, depth = i + m.end(), 1
        while depth:
            depth += {'{': 1, '}': -1}.get(text[j], 0)
            j += 1
        i = j
    return ''.join(out)


# ---- 1. verified files
for name in sorted(os.listdir(SRC)):
    if not name.endswith('.rs') or name == 'trusted.rs':
        continue
    text = open(os.path.join(SRC, name)).read()
    lines = text.split('\n')
    for n, line in enumerate(lines, 1):
        code = line.split('//')[0]
        if line.strip() == '#[cfg(verus_keep_ghost)]' and n < len(lines) \
                and lines[n].strip() == GHOST_IMPORT:
            continue
        if TRUST.search(code) and line.strip() not in ALLOWED.get(name, []):
            fail(f'{name}:{n}: trust construct outside trusted.rs: {line.strip()}')
    rest = strip_attributes(strip_comments(outside_verus(text)))
    rest = re.sub(r'mod\s+\w+\s*\{', '', rest)  # `mod sealed {`: its contents are in verus!
    for stmt in re.split(r'[;\n]', rest):
        s = stmt.strip()
        if not s or s in ('}',) or s.startswith(('#', 'use ', 'pub use ', 'mod ', 'pub mod ')):
            continue
        fail(f'{name}: code outside verus!: {s!r}')
print('verified files: no trust constructs, no code outside verus!' if not failures else '')

# ---- 2. trusted code is upstream's
trusted = open(os.path.join(SRC, 'trusted.rs')).read()
up_block = open(os.path.join(UP, 'block.rs')).read()
up_unwrap = open(os.path.join(UP, 'unwrap_err.rs')).read()
up_utils = open(os.path.join(UP, 'utils.rs')).read()
up_word = open(os.path.join(UP, 'word.rs')).read()
up_seed = open(os.path.join(UP, 'seedable_rng.rs')).read()

# C1: the Debug impl, verbatim (with its comment)
c1 = trusted[trusted.index('// Custom Debug implementation'):].rstrip() + '\n'
print('C1 Debug for BlockRng:', 'verbatim' if c1 in up_block else 'CHANGED')
if c1 not in up_block:
    fail('C1 differs from upstream block.rs')

# C2: panic_msg, the same signature (up to `pub(crate)` and the named return of its contract)
# and body
m = re.search(r'pub\(crate\) fn panic_msg\(err: impl core::error::Error\) -> \(r: Infallible\)'
              r'\s*ensures\s*false,\s*\{\n(.*?)\n\}', trusted, re.S)
up_c2 = re.search(r'fn panic_msg\(err: impl core::error::Error\) -> Infallible \{\n(.*?)\n\}',
                  up_unwrap, re.S)
ok = m and up_c2 and m.group(1) == up_c2.group(1)
print('C2 panic_msg:', 'body verbatim' if ok else 'CHANGED')
if not ok:
    fail('C2 differs from upstream unwrap_err.rs')

# C3, C4: the wrapped statements are upstream's
for cid, stmt, up in (('C3', 'assert!(n < N);', up_block),
                      ('C4', 'assert_eq!(size_of_val(src), size_of::<[W; N]>());', up_utils)):
    ok = stmt in trusted and stmt in up
    print(f'{cid} {stmt}:', 'verbatim' if ok else 'CHANGED')
    if not ok:
        fail(f'{cid}: {stmt} not found in both')

# C5: the wrappers call the standard-library functions that upstream calls
for fn, body, up_body, up in (
        ('u32_to_le_bytes', 'x.to_le_bytes()', 'Self::to_le_bytes(self)', up_word),
        ('u32_from_le_bytes', 'u32::from_le_bytes(b)', 'Self::from_le_bytes(bytes)', up_word),
        ('u64_to_le_bytes', 'x.to_le_bytes()', 'Self::to_le_bytes(self)', up_word),
        ('u64_from_le_bytes', 'u64::from_le_bytes(b)', 'Self::from_le_bytes(bytes)', up_word)):
    m = re.search(r'fn ' + fn + r'\(.*?\{\n\s*(.*?)\n\}', trusted, re.S)
    ok = m and m.group(1).strip() == body and up_body in up
    print(f'C5 {fn}: calls `{body}`' if ok else f'C5 {fn}: CHANGED')
    if not ok:
        fail(f'C5 {fn}')
ok = 'x.to_le_bytes()' in up_seed
print('C5 u32_to_le_bytes in pcg32: upstream calls `x.to_le_bytes()`' if ok else 'C5 pcg32: CHANGED')
if not ok:
    fail('C5 pcg32')

# ---- 3. S7 is vstd's definition
def squash(text):
    return re.sub(r'\s+', '', text)


m = re.search(r'pub axiom fn axiom_spec_u32_from_le_bytes\(s: Seq<u8>\)\s*requires\s*s\.len\(\) == 4,'
              r'\s*ensures\s*vstd::bytes::spec_u32_from_le_bytes\(s\) == (.*?),\s*;', trusted, re.S)
cargo = open(os.path.join(os.path.dirname(SRC), 'Cargo.toml')).read()
ver = re.search(r'vstd = \{ version = "=([^"]+)"', cargo).group(1)
paths = glob.glob(os.path.expanduser(f'~/.cargo/registry/src/*/vstd-{ver}/bytes.rs'))
if not m:
    fail('S7: axiom_spec_u32_from_le_bytes not found in trusted.rs')
elif not paths:
    fail(f'S7: vstd {ver} source (bytes.rs) not found in the cargo registry; run `cargo fetch`')
else:
    vstd_def = re.search(r'pub closed spec fn spec_u32_from_le_bytes\(s: Seq<u8>\) -> u32\s*'
                         r'recommends\s*s\.len\(\) == 4,\s*\{(.*?)\}', open(paths[0]).read(), re.S)
    ok = vstd_def and squash(vstd_def.group(1)) == squash(m.group(1))
    print(f'S7 spec_u32_from_le_bytes: {"vstd" if ok else "DIFFERS FROM vstd"} {ver}: '
          f'{" ".join(m.group(1).split())}')
    if not ok:
        fail('S7 differs from the definition in vstd')

print(f'{failures} failures')
sys.exit(1 if failures else 0)
