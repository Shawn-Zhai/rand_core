#!/usr/bin/env python3
"""Reproduce the findings about the developer's spec (SPEC_REVIEW.md, H1-H5) with Verus.

- H1: `developer_spec/h1_compose.rs` against the developer's crate (`../verus_human_written_spec`):
  both calls fail with "precondition not satisfied".
- H2: `developer_spec/h2_array_size.rs`: vstd cannot prove `size_of::<[u32; 2]>() == 8`.
- H3: a scratch copy of this crate with the developer's (missing) precondition of
  `fill_bytes_via_next_word`: the calls of `next_word` in the body fail.
- H4: a scratch copy of this crate with the developer's precondition of `word_offset` (`N > 0`):
  the `unwrap` in `index` (`into_usize`) can no longer be proved.
- H5: `developer_spec/h5_matching_loop.rs` against the developer's crate runs out of resources;
  `developer_spec/h5_control.rs`, the same client against this crate, fails its assertion at once.

Usage: python3 verus_fixed/verification/developer_spec_findings.py, with `verus` on PATH or
VERUS=/path/to/verus. Exits 1 if any finding does not reproduce."""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CASES = os.path.join(HERE, 'developer_spec')
CRATE = os.path.dirname(HERE)
DEVELOPER = os.path.join(os.path.dirname(CRATE), 'verus_human_written_spec')
VERUS = os.environ.get('VERUS', shutil.which('verus') or 'verus')

failures = 0


def run(args, cwd):
    r = subprocess.run([VERUS] + args, capture_output=True, text=True, cwd=cwd)
    return r.stdout + r.stderr


def errors(out):
    return [l for l in out.splitlines() if l.startswith('error') and 'aborting' not in l]


def check(name, ok, detail):
    global failures
    print(f'{name}: {"reproduced" if ok else "NOT REPRODUCED"}  {detail}')
    failures += not ok


def crate_copy(tmp, src_crate, name):
    dst = os.path.join(tmp, name)
    shutil.copytree(src_crate, dst, ignore=shutil.ignore_patterns('target', 'verification', '.verus-*'))
    return dst


def client(tmp, crate, case):
    """Verify `developer_spec/<case>` against `crate` (exported as `rand_core`)."""
    out_dir = tempfile.mkdtemp(dir=tmp)
    lib, vir = os.path.join(out_dir, 'librand_core.rlib'), os.path.join(out_dir, 'rand_core.vir')
    run(['--crate-type=lib', '--edition=2024', '--crate-name', 'rand_core',
         os.path.join(crate, 'src', 'lib.rs'), '--export', vir, '--compile', '-o', lib], out_dir)
    return run(['--edition=2024', os.path.join(CASES, case), '-o', os.path.join(out_dir, 'client'),
                '--extern', f'rand_core={lib}', '--import', f'rand_core={vir}'], out_dir)


def patched(tmp, name, fname, edits):
    """Verify a copy of this crate with `edits` [(old, new)] applied to `src/<fname>`."""
    crate = crate_copy(tmp, CRATE, name)
    path = os.path.join(crate, 'src', fname)
    text = open(path).read()
    for old, new in edits:
        assert text.count(old) == 1, f'{name}: edit site not found once: {old[:60]!r}'
        text = text.replace(old, new)
    open(path, 'w').write(text)
    return run(['--crate-type=lib', '--edition=2024', os.path.join(crate, 'src', 'lib.rs')], crate)


with tempfile.TemporaryDirectory() as tmp:
    developer = crate_copy(tmp, DEVELOPER, 'developer')

    out = client(tmp, developer, 'h1_compose.rs')
    errs = errors(out)
    check('H1', len(errs) == 2 and all('precondition not satisfied' in e for e in errs),
          f'new -> next_word, reconstruct -> remaining_results: {errs}')

    out = run(['--edition=2024', os.path.join(CASES, 'h2_array_size.rs'), '-o',
               os.path.join(tmp, 'h2')], tmp)
    errs = errors(out)
    check('H2', errs == ['error: postcondition not satisfied'], f'size_of::<[u32; 2]>() == 8: {errs}')

    out = patched(tmp, 'h3', 'utils.rs', [
        ('''    requires
        forall|| next_word.requires(()),
    ensures
        final(dst)@.len() == old(dst)@.len(),''', '''    ensures
        final(dst)@.len() == old(dst)@.len(),'''),
        ('''            next_word == f,
            forall|| next_word.requires(()),''', '''            next_word == f,'''),
    ])
    errs = errors(out)
    check('H3', len(errs) == 2 and all('callee.requires(args)' in e for e in errs),
          f'fill_bytes_via_next_word without a precondition on next_word: {errs}')

    out = patched(tmp, 'h4', 'block.rs', [
        ('''            self.wf() || (N > 0 && exists|i: int|
                1 <= i <= N as int && #[trigger] W::try_from_spec(i as usize) === Ok(
                    self.spec_results()@[0],
                )),
        ensures
            r == if self.buffer().len() == 0 {''', '''            N > 0,
        ensures
            r == if self.buffer().len() == 0 {'''),
        ('''            0 < N,
            self.spec_index() <= N,
        ensures
            r == self.spec_index(),''', '''            0 < N,
        ensures
            r == self.spec_index(),'''),
    ])
    errs = errors(out)
    at_index = 'self.results[0].into_usize()' in out
    check('H4', errs == ['error: precondition not satisfied'] and at_index,
          f'word_offset with only `N > 0`: {errs} (at `into_usize` in `index`: {at_index})')

    out = client(tmp, developer, 'h5_matching_loop.rs')
    loop_errs = errors(out)
    out = client(tmp, CRATE, 'h5_control.rs')
    control_errs = errors(out)
    check('H5', any('rlimit' in e for e in loop_errs) and control_errs == ['error: assertion failed'],
          f'developer\'s crate: {loop_errs}; fixed crate: {control_errs}')

print(f'{failures} findings not reproduced')
sys.exit(1 if failures else 0)
