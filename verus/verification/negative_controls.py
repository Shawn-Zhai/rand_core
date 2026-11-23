#!/usr/bin/env python3
"""Negative controls: inject one bug at a time into a scratch copy of the annotated crate and
check that Verus rejects it. A mutant that verifies would mean the specifications do not
constrain that behaviour.

Usage: python3 verus/verification/negative_controls.py, with `verus` on PATH or
VERUS=/path/to/verus. Exits 1 if any mutant verifies (or if the unmutated crate does not)."""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CRATE = os.path.dirname(HERE)
VERUS = os.environ.get('VERUS', shutil.which('verus') or 'verus')

# (id, description, file, old text, new text). `old` must occur exactly once in `file`. For a
# mutation at several sites of one file, `old` and `new` are lists of the same length.
MUTANTS = [
    ('M1', 'next_word: generate only when index > N (reads results[N] when the buffer is empty)',
     'block.rs', '''        let mut index = self.index();
        if index >= N {
            self.core.generate(&mut self.results);
            index = 0;
            proof {''', '''        let mut index = self.index();
        if index > N {
            self.core.generate(&mut self.results);
            index = 0;
            proof {'''),
    ('M2', 'next_word: does not advance the index (the same word again)',
     'block.rs', '''        let value = self.results[index];
        self.set_index(index + 1);''', '''        let value = self.results[index];
        self.set_index(if index == 0 { 1 } else { index });'''),
    ('M3', 'next_u64_from_u32: words combined big-endian (lo and hi swapped)',
     'block.rs', '(u64::from(hi) << 32) | u64::from(lo)', '(u64::from(lo) << 32) | u64::from(hi)'),
    ('M4', 'next_u64_from_u32: advances by one word instead of two',
     'block.rs', '            new_index = index + 2;', '            new_index = index + 1;'),
    ('M5', 'next_u64_from_u32: empty buffer, keeps the stale last word of the old block as `lo`',
     'block.rs', '''                lo = hi;
                hi = self.results[1];''', '''                hi = self.results[1];'''),
    ('M6', 'fill_bytes: the partially used word is not marked consumed',
     'block.rs', '''                    index += 1;
                    proof {
                        lemma_fill_last(''', '''                    proof {
                        lemma_fill_last('''),
    ('M7', 'fill_bytes: num_chunks ignores the words left in the buffer',
     'block.rs', '''            let num_chunks = if (dest.len() - read_len) / size < N - index {''',
     '''            let num_chunks = if true {'''),
    ('M8', 'fill_bytes: read_len advances by words instead of bytes',
     'block.rs', '            read_len += num_chunks * size;', '            read_len += num_chunks;'),
    ('M9', 'fill_bytes: chunks taken from the start of the remaining words, off by one',
     'block.rs', 'chunk.copy_from_slice(self.results[index + i].to_le_bytes().as_ref());',
     'chunk.copy_from_slice(self.results[index + i - if i > 0 { 1 } else { 0 }].to_le_bytes().as_ref());'),
    ('M10', 'reset_and_skip: skips one word too many',
     'block.rs', '''        let ghost block = self.results;
        self.set_index(n);''', '''        let ghost block = self.results;
        self.set_index(if n + 1 < N { n + 1 } else { n });'''),
    ('M11', 'word_offset: reports N (instead of 0) for an empty buffer',
     'block.rs', '        if index >= N { 0 } else { index }', '        if index > N { 0 } else { index }'),
    ('M12', 'reconstruct: drops the first remaining word',
     'block.rs', '''            results[0] = W::from_usize(index);
            proof {''', '''            results[0] = W::from_usize(if index + 1 < N { index + 1 } else { index });
            proof {'''),
    ('M13', 'next_u64_via_u32: first value in the high half',
     'utils.rs', '    Ok((y << 32) | x)', '    Ok((x << 32) | y)'),
    ('M14', 'fill_bytes_via_next_word: remainder takes the high bytes of the last word',
     'utils.rs', 'rem.copy_from_slice(&val.as_ref()[0..rem.len()]);',
     'rem.copy_from_slice(&val.as_ref()[size - rem.len()..size]);'),
    ('M15', 'read_words: words stored in reverse order',
     'utils.rs', '        dst[i] = W::from_le_bytes(buf);', '        dst[N - 1 - i] = W::from_le_bytes(buf);'),
    ('M16', 'pcg32: multiplier changed',
     'seedable_rng.rs', '    const MUL: u64 = 0x5851_F42D_4C95_7F2D;', '    const MUL: u64 = 0x5851_F42D_4C95_7F2B;'),
    ('M17', 'pcg32: output xorshift by 26 instead of 27',
     'seedable_rng.rs', '    let xorshifted = (((state >> 18) ^ state) >> 27) as u32;',
     '    let xorshifted = (((state >> 18) ^ state) >> 26) as u32;'),
    ('M18', 'seed_from_u64: remainder takes the high bytes of the last output',
     'seedable_rng.rs', 'rem.copy_from_slice(&pcg32(&mut state)[0..rem.len()]);',
     'rem.copy_from_slice(&pcg32(&mut state)[4 - rem.len()..4]);'),
    ('M19', 'Rng::next_u32 (blanket impl) flips a bit of the value',
     'lib.rs', '''        match self.try_next_u32() {
            Ok(x) => x,
        }''', '''        match self.try_next_u32() {
            Ok(x) => x ^ 1,
        }'''),
    ('M20', 'word: u32::from_le_bytes decodes big-endian',
     'word.rs', '''            crate::trusted::u32_from_le_bytes(bytes)''',
     '''            crate::trusted::u32_from_le_bytes([bytes[3], bytes[2], bytes[1], bytes[0]])'''),
    # (Until Verus 0.2026.11.22, M21 mutated this crate's trusted spec of `rotate_right`; vstd now
    # provides that spec. Here code and spec rotate left consistently, so only the test vector
    # can tell.)
    ('M21', 'pcg32 and its spec rotate left instead of right (caught by the PCG32 test vector)',
     'seedable_rng.rs', ['vstd::wrapping::u32_specs::rotate_right(', 'let x = xorshifted.rotate_right(rot);'],
     ['vstd::wrapping::u32_specs::rotate_left(', 'let x = xorshifted.rotate_left(rot);']),
    ('M22', 'TRUSTED spec wrong: to_le_bytes specified big-endian (caught by the PCG32 test vector)',
     'trusted.rs', '''pub open spec fn u32_le_bytes(x: u32) -> Seq<u8> {
    seq![
        (x & 0xff) as u8,
        ((x >> 8u32) & 0xff) as u8,
        ((x >> 16u32) & 0xff) as u8,
        ((x >> 24u32) & 0xff) as u8,
    ]''', '''pub open spec fn u32_le_bytes(x: u32) -> Seq<u8> {
    seq![
        ((x >> 24u32) & 0xff) as u8,
        ((x >> 16u32) & 0xff) as u8,
        ((x >> 8u32) & 0xff) as u8,
        (x & 0xff) as u8,
    ]'''),
]


def verify(src_dir):
    # (run in the scratch crate, so that Verus's output file does not land in the caller's cwd)
    r = subprocess.run([VERUS, '--crate-type=lib', '--edition=2024', os.path.join(src_dir, 'lib.rs')],
                       capture_output=True, text=True, cwd=os.path.dirname(src_dir))
    out = r.stdout + r.stderr
    summary = next((l for l in out.splitlines() if 'verification results' in l), '')
    return r.returncode == 0, summary, out


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        work = os.path.join(tmp, 'crate')
        shutil.copytree(CRATE, work, ignore=shutil.ignore_patterns('target', 'verification', '.verus-*'))
        src = os.path.join(work, 'src')
        ok, summary, _ = verify(src)
        print(f'baseline: {"verifies" if ok else "FAILS"} ({summary.strip()})')
        if not ok:
            sys.exit(1)
        for mid, desc, fname, old, new in MUTANTS:
            path = os.path.join(src, fname)
            orig = open(path).read()
            olds, news = (old, new) if isinstance(old, list) else ([old], [new])
            if any(orig.count(o) != 1 for o in olds):
                print(f'{mid}: mutation site not found exactly once in {fname}')
                failures += 1
                continue
            mutated = orig
            for o, n in zip(olds, news):
                mutated = mutated.replace(o, n)
            open(path, 'w').write(mutated)
            ok, summary, out = verify(src)
            open(path, 'w').write(orig)
            if ok:
                failures += 1
                print(f'{mid}: VERIFIES (not caught!)  {desc}')
            else:
                first = next((l for l in out.splitlines() if l.startswith('error')), '?')
                print(f'{mid}: rejected  {desc}  [{first}]')
    print(f'{len(MUTANTS)} mutants, {len(MUTANTS) - failures} rejected')
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
