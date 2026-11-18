#!/usr/bin/env python3
"""Detect changes that verification made to a crate's executable code.

Both crates (upstream and annotated) are compiled to macro-expanded Rust with `rustc
-Zunpretty=expanded`. In a normal build the `verus!` macro erases ghost code (specifications,
proof blocks, spec and proof functions), so the expanded annotated crate is the code that
actually runs. The two expansions are split into items (functions, impl blocks and their
methods, structs, ...), matched by name rather than by file, so code that only moved between
files or modules is not reported as changed, and compared token by token, ignoring formatting
and comments.

Every difference is reported: changed, added and removed items, imports, crate-level
attributes, other files (Cargo.toml, tests/), and the trust-boundary markers in the annotated
source (`verifier::external`, `external_body`, `assume_specification`, `unsafe`, ...): lines that
are not in upstream, or that occur more often than upstream (a copied upstream line). A
difference passes only if `approved_changes.json` records it with the same fingerprint and a
non-empty `reviewer`. The script never fills in `reviewer`; a human does. If either side of an
approved difference changes, its fingerprint changes and it needs review again.

Each finding in the report links to the item in both crates' source. For an item that a
`macro_rules!` macro generates, the link is the item in the macro's definition, plus the line of
the invocation that generated it.

Not reported as changes: `macro_rules!` definitions that are not exported (they do not run;
their expansions are compared item by item), and the `const _: () = ();` that `verus!` leaves for
an erased `broadcast use`. They are listed in the report for information.

Usage:
    python3 detect_changes.py SOURCE VERUS_FIXED              # check; exit 1 if anything is unreviewed
    python3 detect_changes.py SOURCE VERUS_FIXED --template   # also add unreviewed entries to approvals
SOURCE is the upstream crate (its root, or its `src/`); VERUS_FIXED is the annotated crate (its root,
or a folder such as `verus_fixed/` that contains it). For itoa, from the repository root:
    python3 code_change_detection/detect_changes.py src verus_fixed
Options: --approvals FILE, --report FILE (default: next to this script), --json FILE,
         --toolchain NAME (default: the annotated crate's rust-toolchain.toml),
         --config "CARGO FEATURE FLAGS" (repeatable; default: "--no-default-features" and
         "--all-features").
"""
import argparse
import bisect
import collections
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# ----------------------------------------------------------------------------------- expansion


def toolchain_of(crate):
    path = os.path.join(crate, 'rust-toolchain.toml')
    if os.path.exists(path):
        m = re.search(r'channel\s*=\s*"([^"]+)"', open(path).read())
        if m:
            return m.group(1)
    return None


def crate_root(path, what):
    """The crate at `path`: `path` itself, its parent if `path` is the crate's `src/`, or the one
    subdirectory of `path` that is a crate (`verus_fixed/` -> `verus_fixed/itoa`)."""
    p = os.path.abspath(path)
    if not os.path.isdir(p):
        sys.exit(f'{what}: no such directory: {path}')
    if os.path.exists(os.path.join(p, 'Cargo.toml')):
        return p
    parent = os.path.dirname(p)
    if os.path.basename(p) == 'src' and os.path.exists(os.path.join(parent, 'Cargo.toml')):
        return parent
    subs = sorted(d for d in os.listdir(p) if os.path.exists(os.path.join(p, d, 'Cargo.toml')))
    if len(subs) == 1:
        return os.path.join(p, subs[0])
    sys.exit(f'{what}: {path} is not a crate, the `src/` of one, or a folder with exactly one crate'
             + (f' (found {", ".join(subs)})' if subs else ''))


def expand(crate, flags, toolchain, target_dir):
    """The crate's library, macro-expanded, as rustc sees it in a normal (non-Verus) build."""
    cmd = ['cargo'] + ([f'+{toolchain}'] if toolchain else []) + [
        'rustc', '-q', '--lib', '--target-dir', target_dir] + flags.split() + [
        '--', '-Zunpretty=expanded']
    env = dict(os.environ, RUSTC_BOOTSTRAP='1')  # allows -Z on a stable toolchain
    r = subprocess.run(cmd, cwd=crate, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'expansion failed in {crate} ({" ".join(cmd)}):\n{r.stderr}')
    return r.stdout

# ------------------------------------------------------------------------------- tokenization


TOKEN_RE = re.compile(r'''
    (?P<ws>\s+)
  | (?P<doc>///(?!/)[^\n]*|//![^\n]*)
  | (?P<lcomment>//[^\n]*)
  | (?P<bcomment>/\*)
  | (?P<rawstr>b?r(?P<hashes>\#*)")
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])')
  | (?P<lifetime>'[A-Za-z_]\w*)
  | (?P<num>\d[\w]*(?:\.\d[\w]*)?(?:[eE][+-]?\d+)?)
  | (?P<ident>r\#[A-Za-z_]\w*|[A-Za-z_]\w*)
  | (?P<punct>::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\*=|/=|%=|\^=|&=|\|=|\.\.=|\.\.\.|\.\.|[^\s])
''', re.VERBOSE | re.DOTALL)


def tokenize(text):
    """Tokens as (text, start offset, end offset); comments and whitespace are dropped."""
    toks, i = [], 0
    while i < len(text):
        m = TOKEN_RE.match(text, i)
        kind = m.lastgroup
        if kind == 'bcomment':  # nested block comment
            depth, j = 1, m.end()
            while depth:
                if text.startswith('/*', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('*/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            i = j
            continue
        if kind == 'rawstr':
            end = text.index('"' + m.group('hashes'), m.end()) + 1 + len(m.group('hashes'))
            toks.append((text[i:end], i, end))
            i = end
            continue
        if kind == 'doc':  # `/// text` is `#[doc = " text"]`; `//! text` is `#![doc = ...]`
            toks.append((('DOC:' if m.group()[2] == '/' else 'IDOC:') + m.group()[3:], i, m.end()))
        elif kind not in ('ws', 'lcomment', 'hashes'):
            toks.append((m.group(), i, m.end()))
        i = m.end()
    return normalize_docs(toks)


def unescape(lit):
    """The value of a Rust string literal (the escapes that rustc's printer emits)."""
    body = lit[1:-1]
    return re.sub(r'\\(u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)', lambda m: {
        'n': '\n', 't': '\t', 'r': '\r', '0': '\0', '\\': '\\', '"': '"', "'": "'"}.get(
        m.group(1), chr(int(m.group(1)[2:-1] if m.group(1)[0] == 'u' else m.group(1)[1:], 16))
        if m.group(1)[0] in 'ux' else m.group(1)), body)


def normalize_docs(toks):
    """`#[doc = "x"]` and `#![doc = "x"]` attributes become the same tokens as `///x` and `//!x`."""
    out, i = [], 0
    while i < len(toks):
        t = [x[0] for x in toks[i:i + 6]]
        inner = t[:2] == ['#', '!']
        o = 1 if inner else 0
        if (t[:1] == ['#'] and len(t) >= 6 + o - 1 and t[1 + o:4 + o] == ['[', 'doc', '=']
                and i + 5 + o < len(toks) and toks[i + 5 + o][0] == ']'
                and toks[i + 4 + o][0].startswith('"')):
            text = unescape(toks[i + 4 + o][0])
            out.append((('IDOC:' if inner else 'DOC:') + text, toks[i][1], toks[i + 5 + o][2]))
            i += 6 + o
            continue
        out.append(toks[i])
        i += 1
    return out


def drop_trailing_commas(toks):
    """Remove `,` before a closing bracket: the printer adds them when it wraps a line. Kept in
    one-element tuples, where `(x,)` and `(x)` differ."""
    out = []
    for k, t in enumerate(toks):
        if t[0] == ',' and k + 1 < len(toks) and toks[k + 1][0] in ')]}':
            if toks[k + 1][0] == ')':
                depth, other_comma = 0, False
                for x in reversed(out):
                    if x[0] in ')]}':
                        depth += 1
                    elif x[0] in '([{':
                        if depth == 0:
                            break
                        depth -= 1
                    elif x[0] == ',' and depth == 0:
                        other_comma = True
                        break
                if not other_comma:
                    out.append(t)
            continue
        out.append(t)
    return out


def drop_erased_blocks(toks):
    """Remove what `verus!` leaves of erased ghost code: `{}` statements (from `proof { ... }`),
    then `else {}` (from an `else` that held only a proof block), and `const _: () = ();` items
    (from a module-level `broadcast use`). None of them does anything."""
    unit_const = ['const', '_', ':', '(', ')', '=', '(', ')', ';']
    texts = [t[0] for t in toks]
    keep, k = [], 0
    while k < len(toks):
        if texts[k:k + 9] == unit_const and (k == 0 or texts[k - 1] in (';', '{', '}', ']')):
            k += 9
            continue
        keep.append(toks[k])
        k += 1
    toks, out = keep, []
    for t in toks:
        if (t[0] == '}' and out and out[-1][0] == '{' and len(out) >= 2
                and out[-2][0] in (';', '{', '}')):
            out.pop()
            continue
        out.append(t)
    toks, out = out, []
    for t in toks:
        if t[0] == '}' and len(out) >= 2 and out[-1][0] == '{' and out[-2][0] == 'else':
            del out[-2:]
            continue
        out.append(t)
    return out

# ------------------------------------------------------------------------------- item parsing

OPEN, CLOSE = '([{', ')]}'
ITEM_KINDS = ('fn', 'struct', 'enum', 'union', 'trait', 'impl', 'mod', 'use', 'type',
              'const', 'static', 'extern', 'macro_rules')
SEMI_ITEMS = ('use', 'type', 'const', 'static', 'extern')


def match_close(toks, i):
    """Index of the bracket that closes toks[i]."""
    depth = 0
    for j in range(i, len(toks)):
        if toks[j][0] in OPEN:
            depth += 1
        elif toks[j][0] in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced brackets')


def strip_generics(toks):
    """Header tokens without `<...>` groups and lifetimes: `impl<'a, T> X for &'a S<T>` -> X for &S."""
    out, depth = [], 0
    for t in toks:
        if t == '<':
            depth += 1
        elif t == '>' and depth:
            depth -= 1
        elif depth == 0 and not t.startswith("'"):
            out.append(t)
    return out


def parse_items(toks, lo, hi, path, out):
    """Append (key, module path, kind, token slice) for every item in toks[lo:hi]."""
    i = lo
    while i < hi:
        start = i
        while i < hi and (toks[i][0] == '#' or toks[i][0].startswith(('DOC:', 'IDOC:'))):
            if toks[i][0] == '#':  # attribute
                i = match_close(toks, i + (2 if toks[i + 1][0] == '!' else 1)) + 1
            else:
                i += 1
        if i < hi and toks[i][0] == ';':
            i += 1
            continue
        if i >= hi:
            break
        # visibility and qualifiers
        j = i
        if toks[j][0] == 'pub':
            j += 1
            if toks[j][0] == '(':
                j = match_close(toks, j) + 1
        while toks[j][0] in ('unsafe', 'async', 'default', 'auto', 'const') and \
                toks[j + 1][0] in ('fn', 'impl', 'trait', 'unsafe', 'async', 'extern', 'const'):
            j += 1  # qualifiers: `const fn`, `unsafe fn`, `unsafe impl`, ...
        if toks[j][0] == 'extern' and toks[j + 1][0].startswith('"'):
            j += 2  # extern "C" fn
        kind = toks[j][0]
        if kind not in ITEM_KINDS:
            raise ValueError(f'unexpected token {kind!r} in {"::".join(path) or "crate"}')
        # end of the item
        k = j
        end = None
        while k < hi:
            t = toks[k][0]
            if t == ';' and (kind in SEMI_ITEMS or end is None):
                end = k
                break
            if t == '{' and kind not in SEMI_ITEMS:
                end = match_close(toks, k)
                break
            if t in '([':
                k = match_close(toks, k)
            k += 1
        if kind in SEMI_ITEMS:
            k = j
            while toks[k][0] != ';':
                k = match_close(toks, k) if toks[k][0] in OPEN else k
                k += 1
            end = k
        name = toks[j + 1][0] if j + 1 < hi else ''
        body = toks[start:end + 1]
        if kind == 'impl':
            hdr_end = next(x for x in range(j, end + 1) if toks[x][0] in ('{', 'where'))
            header = ' '.join(strip_generics([t[0] for t in toks[j + 1:hdr_end]]))
            brace = next(x for x in range(j, end + 1) if toks[x][0] == '{')
            members = []
            parse_items(toks, brace + 1, end, path, members)
            if members or ' for ' in f' {header} ':  # an empty inherent impl is erased ghost code
                out.append((f'impl {header}', path, 'impl', toks[start:brace + 1] + [toks[end]]))
            for key, _, mkind, mtoks in members:
                out.append((f'impl {header} :: {key}', path, mkind, mtoks))
        elif kind == 'mod' and toks[end][0] == '}':
            brace = next(x for x in range(j, end + 1) if toks[x][0] == '{')
            parse_items(toks, brace + 1, end, path + [name], out)
        elif kind == 'use' or kind == 'extern':
            out.append((' '.join(t[0] for t in toks[i:end + 1]), path, kind, body))
        elif kind == 'macro_rules':
            out.append((f'macro_rules {toks[j + 2][0]}', path, kind, body))
        else:
            out.append((f'{kind} {name}', path, kind, body))
        i = end + 1


def items_of(text):
    toks = drop_trailing_commas(drop_erased_blocks(tokenize(text)))
    out = []
    # The crate's inner attributes and docs (`#![no_std]`, `#![allow(...)]`, `//! ...`) form one
    # item of their own; otherwise they would be attached to the first item and missed.
    i = 0
    while i < len(toks) and (toks[i][0].startswith('IDOC:') or
                             (toks[i][0] == '#' and toks[i + 1][0] == '!')):
        i = match_close(toks, i + 2) + 1 if toks[i][0] == '#' else i + 1
    if i:
        out.append(('crate attributes', [], 'attrs', toks[:i]))
    parse_items(toks, i, len(toks), [], out)
    items = {}
    for key, path, kind, itoks in out:
        if kind == 'impl':  # a type may have several impl blocks: compare their distinct headers
            hdr = [t[0] for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
            same = [k for k, v in items.items() if v['kind'] == 'impl' and
                    (k == key or k.startswith(key + ' #'))]
            if any([t[0] for t in items[k]['toks'] if not t[0].startswith(('DOC:', 'IDOC:'))] == hdr
                   for k in same):
                continue
            if same:
                key = f"{key} #{len(same) + 1}"
        elif kind in ('use', 'extern'):  # imports are compared per module: key them by module
            key = '::'.join(path + [key])
            n = 1
            while key in items:  # the same import twice in one module
                key = '::'.join(path + [f'{key.split("::")[-1]} #{n}'])
                n += 1
        elif key in items or key.endswith(' _'):
            # same name in two modules: keep both, qualified; anonymous items (`const _`) and any
            # remaining clash are numbered in order of appearance
            if key in items and not key.endswith(' _'):
                key = '::'.join(path + [key])
            if key in items or key.endswith(' _'):
                base, n = key, 1
                while f'{base} #{n}' in items:
                    n += 1
                key = f'{base} #{n}'
        items[key] = dict(path=path, kind=kind, toks=itoks)
    return items


def split_docs(itoks):
    """(doc lines, other tokens): documentation is compared separately from code."""
    docs = [t[0].split(':', 1)[1] for t in itoks if t[0].startswith(('DOC:', 'IDOC:'))]
    rest = [t[0] for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
    return docs, rest


def source_of(text, itoks):
    """The item's expanded text, without comments and erased `{}` lines, for display."""
    code = [t for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
    chunk = text[code[0][1]:code[-1][2]]
    chunk = re.sub(r'(?<=[{;])\s*\{\}', '', chunk)
    chunk = re.sub(r'\s*else\s*\{\s*\}', '', chunk)
    lines = [l for l in chunk.split('\n')
             if l.strip() not in ('{}', '') and not l.strip().startswith('//')]
    indent = min((len(l) - len(l.lstrip()) for l in lines[1:]), default=0)
    return [lines[0].strip()] + [l[min(indent, len(l) - len(l.lstrip())):] for l in lines[1:]]

# --------------------------------------------------------------------------- source locations

ITEM_WORDS = ('fn', 'const', 'type', 'static', 'struct', 'enum', 'union', 'trait', 'mod',
              'macro_rules')


def item_end(toks, k):
    """Index of the last token of the item whose keyword is toks[k]."""
    depth = 0
    for x in range(k, len(toks)):
        t = toks[x][0]
        if t in ('(', '['):
            depth += 1
        elif t in (')', ']'):
            depth -= 1
        elif depth == 0 and t == ';':
            return x
        elif depth == 0 and t == '{':
            return match_close(toks, x)
    return len(toks) - 1


def bind(pattern, args, text):
    """Bind the metavariables of a `macro_rules!` arm's pattern (tokens) to the text of an
    invocation's arguments (tokens with offsets into `text`). None if the arm does not match.
    Handles `$x:frag` and literal tokens; repetitions `$(...)*` are not supported."""
    elems, i = [], 0
    while i < len(pattern):
        if pattern[i] == '$' and i + 3 < len(pattern) and pattern[i + 2] == ':':
            elems.append(('var', pattern[i + 1], pattern[i + 3]))
            i += 4
        else:
            elems.append(('lit', pattern[i]))
            i += 1
    out, j = {}, 0
    for n, e in enumerate(elems):
        if e[0] == 'lit':
            if j >= len(args) or args[j][0] != e[1]:
                return None
            j += 1
        elif e[2] in ('ident', 'literal', 'lifetime', 'tt'):
            if j >= len(args):
                return None
            out[e[1]] = text[args[j][1]:args[j][2]]
            j += 1
        else:  # ty, expr, path, pat, ...: everything up to the next literal token of the pattern
            stop = next((x[1] for x in elems[n + 1:] if x[0] == 'lit'), None)
            start, depth = j, 0
            while j < len(args) and not (depth == 0 and args[j][0] == stop):
                depth += (args[j][0] in OPEN) - (args[j][0] in CLOSE)
                j += 1
            if j == start:
                return None
            out[e[1]] = text[args[start][1]:args[j - 1][2]]
    return out if j == len(args) else None


class SourceIndex:
    """Where items are in a crate's source, for the links in the report. The expanded code that
    is compared has no file or line information, so each item is looked up again in the source:
    by kind and name, and an impl's member inside the impl with the same header. Macro-generated
    items are looked up in each `macro_rules!` body with the invocation's arguments substituted
    (line numbers are kept, so a match is a line of the macro's definition). When several places
    match (instances of one macro, `cfg` variants, `const _`), the one whose tokens are closest
    to the expanded item is chosen. This is a lookup for the reader, not part of the check."""

    def __init__(self, crate):
        self.crate = crate
        self.docs = []  # dict(path, toks, line(offset) -> line, macro, call=(path, line))
        files = []
        for root, _, names in os.walk(os.path.join(crate, 'src')):
            files += [os.path.join(root, f) for f in names if f.endswith('.rs')]
        files.sort(key=lambda f: (os.path.basename(f) != 'lib.rs', f))
        macros, raw = {}, []
        for path in files:
            text = open(path).read()
            rel = os.path.relpath(path, crate)
            toks = tokenize(text)
            blank = list(text)
            for k in range(len(toks) - 3):
                if toks[k][0] != 'macro_rules' or toks[k + 1][0] != '!':
                    continue
                arms, a = [], k + 4
                close = match_close(toks, k + 3)
                while a < close and toks[a][0] in OPEN:
                    p_close = match_close(toks, a)
                    b_open = p_close + 2  # after `=>`
                    b_close = match_close(toks, b_open)
                    arms.append(([t[0] for t in toks[a + 1:p_close]],
                                 toks[b_open][2], toks[b_close][1]))
                    a = b_close + 1 + (b_close + 1 < close and toks[b_close + 1][0] == ';')
                macros[toks[k + 2][0]] = (rel, text, arms)
                for _, lo, hi in arms:  # the bodies are searched only through their instances
                    for x in range(lo, hi):
                        if blank[x] != '\n':
                            blank[x] = ' '
            raw.append((rel, text, ''.join(blank)))
        for rel, text, blank in raw:
            starts = self._line_starts(text)
            btoks = tokenize(blank)
            self.docs.append(dict(path=rel, toks=btoks, line=self._liner(starts, 1), macro=None,
                                  call=None))
            for k in range(len(btoks) - 2):  # invocations: NAME ! ( ... )
                name = btoks[k][0]
                if name not in macros or btoks[k + 1][0] != '!' or btoks[k + 2][0] not in OPEN:
                    continue
                if k and btoks[k - 1][0] == 'macro_rules':
                    continue
                args = btoks[k + 3:match_close(btoks, k + 2)]
                mrel, mtext, arms = macros[name]
                for pattern, lo, hi in arms:
                    b = bind(pattern, args, blank)
                    if b is None:
                        continue
                    body = re.sub(r'\$(\w+)', lambda m: b.get(m.group(1), m.group(0)).replace(
                        '\n', ' '), mtext[lo:hi])
                    first = mtext.count('\n', 0, lo) + 1
                    self.docs.append(dict(path=mrel, toks=tokenize(body), macro=name,
                                          line=self._liner(self._line_starts(body), first),
                                          call=(rel, text.count('\n', 0, btoks[k][1]) + 1)))
                    break

    @staticmethod
    def _line_starts(text):
        return [0] + [m.end() for m in re.finditer('\n', text)]

    @staticmethod
    def _liner(starts, first):
        return lambda off: first + bisect.bisect_right(starts, off) - 1

    def _loc(self, doc, k, end):
        return dict(path=doc['path'], line=doc['line'](doc['toks'][k][1]),
                    end=doc['line'](doc['toks'][end][2] - 1), macro=doc['macro'], call=doc['call'])

    def locate(self, key, itoks=()):
        """The source location of the item with this key (as `items_of` names it), or None."""
        lib = next((d for d in self.docs if d['macro'] is None and d['path'] == os.path.join(
            'src', 'lib.rs')), self.docs[0] if self.docs else None)
        if key == 'crate attributes' and lib:
            t, k = lib['toks'], 0
            while k < len(t) and t[k][0].startswith('IDOC:'):
                k += 1
            if k + 1 < len(t) and t[k][0] == '#' and t[k + 1][0] == '!':
                e = k
                while e + 1 < len(t) and t[e][0] == '#' and t[e + 1][0] == '!':
                    e = match_close(t, e + 2) + 1
                return self._loc(lib, k, e - 1)
            return None
        if key == 'imports' and lib:
            k = next((x for x, t in enumerate(lib['toks']) if t[0] == 'use'), None)
            return None if k is None else self._loc(lib, k, item_end(lib['toks'], k))
        key = re.sub(r' #\d+$', '', re.sub(r'^(\w+::)+', '', key))
        m = re.match(r'^impl (.*?)(?: :: ((?:%s) \S+))?$' % '|'.join(ITEM_WORDS), key)
        header, member = (m.group(1), m.group(2)) if m else (None, key)
        cands = []
        for doc in self.docs:
            t = doc['toks']
            spans = []
            if header is not None:
                for k in range(len(t)):
                    if t[k][0] != 'impl':
                        continue
                    h = next((x for x in range(k, len(t)) if t[x][0] in ('{', 'where', ';')), None)
                    if h is None or ' '.join(strip_generics([x[0] for x in t[k + 1:h]])) != header:
                        continue
                    brace = next(x for x in range(h, len(t)) if t[x][0] == '{')
                    spans.append((k, brace, match_close(t, brace)))
            else:
                spans.append((None, -1, len(t)))
            for k, lo, hi in spans:
                if member is None:
                    cands.append((doc, k, hi))
                    continue
                kind, name = member.split(' ', 1)
                depth = 0
                for x in range(lo + 1, hi):
                    w = t[x][0]
                    if header is not None:
                        if w in OPEN:
                            depth += 1
                        elif w in CLOSE:
                            depth -= 1
                    if depth or w != kind or x + 2 >= len(t):
                        continue
                    if t[x + 1][0] == name or (kind == 'macro_rules' and t[x + 2][0] == name):
                        if x and t[x - 1][0] == '.':
                            continue
                        cands.append((doc, x, item_end(t, x)))
        if not cands:
            return None
        if len(cands) > 1 and itoks:
            want = [x[0] for x in itoks if not x[0].startswith(('DOC:', 'IDOC:'))]
            cands.sort(key=lambda c: -difflib.SequenceMatcher(None, [
                x[0] for x in c[0]['toks'][c[1]:c[2] + 1] if not x[0].startswith(('DOC:', 'IDOC:'))],
                want, autojunk=False).ratio())
        doc, k, end = cands[0]
        return self._loc(doc, k, end)


def link(loc, crate, report_dir):
    """Markdown link to a location, relative to the report."""
    if not loc:
        return 'not located'
    path = os.path.relpath(os.path.join(crate, loc['path']), report_dir)
    if loc.get('line') is None:
        return f"[{loc['path']}]({path})"
    l1, l2 = loc['line'], loc.get('end') or loc['line']
    text = f"{loc['path']}:{l1}" + (f'-{l2}' if l2 != l1 else '')
    s = f"[{text}]({path}#L{l1}" + (f'-L{l2}' if l2 != l1 else '') + ')'
    if loc.get('macro'):
        cpath, cline = loc['call']
        s += (f" in `{loc['macro']}!`, invoked at [{cpath}:{cline}]"
              f"({os.path.relpath(os.path.join(crate, cpath), report_dir)}#L{cline})")
    return s

# ---------------------------------------------------------------------------------------- hints

HINTS = [  # (description, pattern on removed lines or None, pattern on added lines or None)
    ('`debug_assert*!` removed (debug builds no longer check it)', r'if true \{|assert_failed', None),
    ('`get_unchecked(_mut)` -> verified stand-in from std_ext.rs', r'get_unchecked(_mut)?\(',
     r'\b(write_unchecked|get_unchecked)\(&?'),
    ('`MaybeUninit::write` -> assignment of `MaybeUninit::new(..)`', r'\]\s*\.write\(',
     r'= MaybeUninit::new\('),
    ('byte literal or byte string -> numbers', r"b'.'|\*b\"", None),
    ('`unsigned_abs()` -> in-range cast expression', r'unsigned_abs\(\)', r'as \w+ \+ 1'),
    ('`for .. in (..).rev()` -> `while` loop', r'\.rev\(\)', r'^\s*while\b'),
    ('`MAX_STR_LEN` -> plain constant of `private`',
     r'ilog10\(\)|<\w+ as Integer>::MAX_STR_LEN|MAX_STR_LEN\]',
     r'private::\w+_MAX_STR_LEN'),
    ('raw-pointer cast -> trusted `buffer_of`', r'as_mut_ptr\(\)\.cast', r'buffer_of::'),
    ('signed formatting -> verified `Signed::fmt`', r'try_into\(\)\.unwrap\(\)', r'Signed::fmt\('),
    ('`fmt` generic over the buffer length `N`', r'Self::Buffer', r'const N\s*:\s*usize'),
    ('visibility widened to `pub(crate)`', None, r'^\s*pub\(crate\) '),
]


def hints(diff, new_fns=()):
    removed = [l[1:] for l in diff if l.startswith('-') and not l.startswith('---')]
    added = [l[1:] for l in diff if l.startswith('+') and not l.startswith('+++')]
    out = []
    for desc, rem, add in HINTS:
        if (rem is None or any(re.search(rem, l) for l in removed)) and \
                (add is None or any(re.search(add, l) for l in added)):
            out.append(desc)
    called = sorted({n for n in new_fns for l in added if re.search(rf'\b{n}\(', l)} -
                    {n for n in new_fns for l in removed if re.search(rf'\b{n}\(', l)})
    if called:
        out.append('calls functions that verification added: ' + ', '.join(f'`{n}`' for n in called))
    return out

# --------------------------------------------------------------------------------- comparison


def fingerprint(*parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(json.dumps(p).encode())
        h.update(b'\0')
    return h.hexdigest()[:16]


def import_lines(items):
    return sorted(f"{'::'.join(v['path']) or 'crate'}: {k.split('::', 1)[-1] if v['path'] and k.startswith('::'.join(v['path']) + '::') else k}"
                  for k, v in items.items() if v['kind'] in ('use', 'extern'))


def compare(up_text, ann_text, config, up_index, ann_index):
    up, ann = items_of(up_text), items_of(ann_text)
    findings = []
    ui, ai = import_lines(up), import_lines(ann)
    if ui != ai:
        findings.append(dict(key='imports', status='changed', config=config, kind='use',
                             fp=fingerprint(ui, ai),
                             diff=[l for l in difflib.unified_diff(ui, ai, 'upstream', 'annotated',
                                                                   lineterm='', n=0)
                                   if not l.startswith('@@')]))
    up = {k: v for k, v in up.items() if v['kind'] not in ('use', 'extern')}
    ann = {k: v for k, v in ann.items() if v['kind'] not in ('use', 'extern')}
    for key in sorted(set(up) | set(ann)):
        u, a = up.get(key), ann.get(key)
        x = a or u
        if x['kind'] == 'macro_rules' and not any(
                'macro_export' in [t[0] for t in v['toks']] for v in (u, a) if v):
            if not (u and a and split_docs(u['toks']) == split_docs(a['toks'])):
                findings.append(dict(key=key, status='macro', config=config, kind='macro_rules',
                                     note='changed' if u and a else ('added' if a else 'removed')))
            continue
        if u and a:
            udocs, ucode = split_docs(u['toks'])
            adocs, acode = split_docs(a['toks'])
            what = []
            if ucode != acode:
                what.append('code')
            if udocs != adocs:
                what.append('docs')
            if not what:
                if u['path'] != a['path']:
                    findings.append(dict(key=key, status='moved', config=config, kind=u['kind'],
                                         note=f"{'::'.join(u['path']) or 'crate'} -> "
                                              f"{'::'.join(a['path']) or 'crate'}"))
                continue
            status = 'changed' if 'code' in what else 'docs changed'
            diff = list(difflib.unified_diff(source_of(up_text, u['toks']),
                                             source_of(ann_text, a['toks']),
                                             'upstream', 'annotated', lineterm='', n=2))
            findings.append(dict(key=key, status=status, config=config, kind=u['kind'],
                                 fp=fingerprint(ucode, acode, udocs, adocs), diff=diff))
        elif a:
            _, acode = split_docs(a['toks'])
            findings.append(dict(key=key, status='added', config=config, kind=a['kind'],
                                 fp=fingerprint(None, acode),
                                 diff=['+' + l for l in source_of(ann_text, a['toks'])]))
        else:
            _, ucode = split_docs(u['toks'])
            findings.append(dict(key=key, status='removed', config=config, kind=u['kind'],
                                 fp=fingerprint(ucode, None),
                                 diff=['-' + l for l in source_of(up_text, u['toks'])]))
    for f in findings:  # where each item is in the two crates' source, for the report's links
        k = f['key']
        for side, items, index in (('up_loc', up, up_index), ('ann_loc', ann, ann_index)):
            item = items.get(k)
            f[side] = index.locate(k, item['toks'] if item else ()) if item or k == 'imports' else None
    return findings


def compare_files(upstream, annotated):
    """Non-library files: Cargo.toml and tests/ must match, or be approved."""
    findings = []
    names = ['Cargo.toml', 'rust-toolchain.toml']
    for d in ('tests', 'benches', 'examples'):
        for root in (upstream, annotated):
            if os.path.isdir(os.path.join(root, d)):
                names += [os.path.join(d, f) for f in os.listdir(os.path.join(root, d))]
    for name in sorted(set(names)):
        up_p, ann_p = os.path.join(upstream, name), os.path.join(annotated, name)
        u = open(up_p).read().split('\n') if os.path.exists(up_p) else None
        a = open(ann_p).read().split('\n') if os.path.exists(ann_p) else None
        if u == a:
            continue
        diff = list(difflib.unified_diff(u or [], a or [], 'upstream', 'annotated',
                                         lineterm='', n=1))
        status = 'changed' if u and a else ('added' if a else 'removed')
        findings.append(dict(key=f'file {name}', status=status, config='files', kind='file',
                             fp=fingerprint(u, a), diff=diff,
                             up_loc=dict(path=name, line=None) if u is not None else None,
                             ann_loc=dict(path=name, line=None) if a is not None else None))
    return findings


# Lines that make code trusted rather than verified, or where the program Verus checks (built
# with `verus_keep_ghost`) and the program that runs (built without it) can differ.
TRUST_RE = re.compile(r'verifier::external\b|external_body|external_fn_specification|'
                      r'assume_specification|\badmit\s*\(|\bassume\s*\(|\baxiom\b|'
                      r'\buninterp\b|verifier::(?:truncate|exec_allows_no_decreases_clause|'
                      r'assume_termination|nonlinear)|\bunsafe\b|verus_keep_ghost')


def trust_markers(upstream, annotated):
    """Lines in the annotated source that make something trusted rather than verified (or that
    add `unsafe`): each line that is not in upstream's source, and each line that is but occurs
    more often than upstream (a copy of an upstream line in new code is new trust too)."""
    up_count = collections.Counter()
    for root, _, files in os.walk(os.path.join(upstream, 'src')):
        for f in files:
            if f.endswith('.rs'):
                up_count.update(l.strip() for l in open(os.path.join(root, f)))
    occurrences = []  # (path, line number, raw text, text shown)
    src = os.path.join(annotated, 'src')
    for root, _, files in os.walk(src):
        for f in sorted(files):
            if not f.endswith('.rs'):
                continue
            path = os.path.relpath(os.path.join(root, f), annotated)
            src_lines = open(os.path.join(root, f)).read().split('\n')
            for n, line in enumerate(src_lines, 1):
                s = line.strip()
                if s.startswith('//') or not TRUST_RE.search(s):
                    continue
                shown = s
                if s.startswith('#['):  # an attribute: show the item it applies to
                    nxt = next((l.strip() for l in src_lines[n:] if l.strip() and not
                                l.strip().startswith(('#[', '//'))), '')
                    shown = f'{s} {nxt}'
                occurrences.append((path, n, s, shown))
    ann_count = collections.Counter(o[2] for o in occurrences)
    out, seen = [], set()
    for path, n, s, shown in sorted(occurrences, key=lambda o: (o[0], o[1])):
        if not up_count[s]:
            # one entry per distinct (file, text); keep the first line number
            key = f'trust {path}: {shown}'
            if key not in seen:
                seen.add(key)
                out.append(dict(key=key, status='trust marker', config='source', kind='trust',
                                line=n, fp=fingerprint(path, shown), up_loc=None,
                                ann_loc=dict(path=path, line=n)))
        elif ann_count[s] > up_count[s] and s not in seen:
            # an upstream line, copied: one entry listing every occurrence, since any of them
            # may be the new one
            seen.add(s)
            locs = [o for o in occurrences if o[2] == s]
            out.append(dict(key=f'trust more often than upstream: {shown}', status='trust marker',
                            config='source', kind='trust', line=n,
                            fp=fingerprint('count', s, up_count[s], [o[0] for o in locs]),
                            up_loc=None, ann_loc=[dict(path=o[0], line=o[1]) for o in locs],
                            count_note=f'{len(locs)} here; upstream has {up_count[s]}'))
    return out

# ---------------------------------------------------------------------------------- reporting


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('source', help="the upstream crate (its root or its src/)")
    ap.add_argument('verus_fixed', help='the annotated crate (its root, or a folder that contains it)')
    ap.add_argument('--approvals', default=os.path.join(HERE, 'approved_changes.json'))
    ap.add_argument('--report', default=os.path.join(HERE, 'changes_report.md'))
    ap.add_argument('--toolchain', default=None)
    ap.add_argument('--config', action='append')
    ap.add_argument('--template', action='store_true',
                    help='add unreviewed findings to the approvals file, with an empty reviewer')
    ap.add_argument('--json', help='also write the findings, with their review status, here')
    args = ap.parse_args()
    upstream = crate_root(args.source, 'SOURCE')
    annotated = crate_root(args.verus_fixed, 'VERUS_FIXED')
    toolchain = args.toolchain or toolchain_of(annotated)
    configs = args.config or ['--no-default-features', '--all-features']

    findings = []
    up_index, ann_index = SourceIndex(upstream), SourceIndex(annotated)
    with tempfile.TemporaryDirectory(prefix='detect-changes-') as tmp:
        for cfg in configs:
            up = expand(upstream, cfg, toolchain, os.path.join(tmp, 'up'))
            ann = expand(annotated, cfg, toolchain, os.path.join(tmp, 'ann'))
            findings += compare(up, ann, cfg, up_index, ann_index)
    findings += compare_files(upstream, annotated)
    findings += trust_markers(upstream, annotated)

    # merge the same finding seen under several configurations
    merged = {}
    for f in findings:
        k = (f['key'], f['status'], f.get('fp'))
        if k in merged:
            merged[k]['config'] += f", {f['config']}"
        else:
            merged[k] = f
    findings = list(merged.values())

    approvals = json.load(open(args.approvals)) if os.path.exists(args.approvals) else []
    approved = {(e['key'], e['fingerprint']): e for e in approvals if e.get('reviewer')}
    entries = {(e['key'], e['fingerprint']): e for e in approvals}
    for f in findings:
        if f['status'] in ('moved', 'macro'):
            f['review'] = 'info'
        else:
            e = approved.get((f['key'], f['fp']))
            f['review'] = f"approved by {e['reviewer']}" if e else 'UNREVIEWED'
            f['note'] = (e or {}).get('note', '')
            f['agent_note'] = entries.get((f['key'], f['fp']), {}).get('agent_note', '')
    pending = [f for f in findings if f['review'] == 'UNREVIEWED']
    stale = [e for e in approvals if e.get('reviewer') and
             not any(f['key'] == e['key'] and f.get('fp') == e['fingerprint'] for f in findings)]

    order = ['changed', 'added', 'removed', 'docs changed', 'trust marker', 'moved', 'macro']
    new_fns = {m.group(1) for f in findings if f['status'] == 'added'
               for m in [re.search(r'\bfn (\w+)$', f['key'])] if m}
    findings.sort(key=lambda f: (order.index(f['status']), f['kind'] == 'file', f['key']))
    for f in findings:
        f['hints'] = hints(f.get('diff', []), new_fns) if f['status'] == 'changed' else []
    report_dir = os.path.dirname(os.path.abspath(args.report))
    rep = ['# Changes made by verification', '',
           'Generated by `detect_changes.py`. Each item of the annotated crate, with Verus ghost code',
           'erased (as in a normal build), is compared with the same item upstream, matched by name.',
           'Ignored: formatting, comments, trailing commas, the empty `{}`, `else {}` and',
           '`const _: () = ();` that erased ghost code leaves, and which file or module an item is in.',
           'Documentation is compared separately. Hints are heuristics to speed up review, not checks.',
           'Source and Annotated link each item in the two crates (for a macro-generated item: in the',
           "macro's definition, and the invocation); they are looked up after the comparison.", '',
           f'- Upstream: `{os.path.relpath(upstream, os.path.dirname(os.path.abspath(args.report)))}`',
           f'- Annotated: `{os.path.relpath(annotated, os.path.dirname(os.path.abspath(args.report)))}`',
           f'- Toolchain: `{toolchain}`; configurations: ' + ', '.join(f'`{c}`' for c in configs), '',
           '| finding | count | unreviewed |', '|---|---|---|']
    for st in order:
        fs = [f for f in findings if f['status'] == st]
        if fs:
            rep.append(f"| {st} | {len(fs)} | {sum(f['review'] == 'UNREVIEWED' for f in fs)} |")
    if stale:
        rep += ['', f'**{len(stale)} approvals match nothing** (the code changed since review, or the '
                'change was undone):'] + [f"- `{e['key']}`" for e in stale]
    titles = {'changed': 'Changed', 'added': 'Added (not upstream)', 'removed': 'Removed',
              'docs changed': 'Documentation changed', 'trust marker': 'Trust boundary (lines '
              'that make code trusted rather than verified, or add `unsafe`, and that are new or '
              'occur more often than upstream)'}
    for st in order[:-2]:
        fs = [f for f in findings if f['status'] == st]
        if not fs:
            continue
        rep += ['', f'## {titles[st]}']
        for f in fs:
            rep += ['', f"### `{f['key']}`", '',
                    f"Review: **{f['review']}**" + (f" — {f['note']}" if f.get('note') else '')
                    + (f"  \nAgent's explanation (to be checked): {f['agent_note']}"
                       if f.get('agent_note') else '')
                    + f"  \nConfigurations: {f['config']}  \nFingerprint: `{f['fp']}`"
                    + (f"  \nSource: {link(f['up_loc'], upstream, report_dir)}"
                       if f.get('up_loc') or f['status'] in ('changed', 'removed', 'docs changed') else '')
                    + (f"  \nOccurrences: {f['count_note']}" if f.get('count_note') else '')
                    + (f"  \nAnnotated: {', '.join(link(l, annotated, report_dir) for l in f['ann_loc']) if isinstance(f.get('ann_loc'), list) else link(f['ann_loc'], annotated, report_dir)}"
                       if f.get('ann_loc') or f['status'] in ('changed', 'added', 'docs changed') else '')
                    + (''.join(f"  \nHint: {h}" for h in f['hints']))]
            if f.get('diff'):
                rep += ['', '```diff'] + f['diff'] + ['```']
    moved = [f for f in findings if f['status'] == 'moved']
    if moved:
        rep += ['', '## Moved, otherwise unchanged (information only)', '',
                '| item | from -> to |', '|---|---|'] + [f"| `{f['key']}` | {f['note']} |" for f in moved]
    macros = [f for f in findings if f['status'] == 'macro']
    if macros:
        rep += ['', '## Macro definitions (information only)', '',
                'Not exported, so they do not run themselves: the items they expand to are compared '
                'above.', '', '| macro | definition |', '|---|---|'] + [
                    f"| `{f['key']}` | {f['note']} |" for f in macros]
    open(args.report, 'w').write('\n'.join(rep) + '\n')

    if args.json:
        json.dump([{k: f.get(k) for k in ('key', 'status', 'review', 'fp', 'config', 'hints',
                                          'up_loc', 'ann_loc')}
                   for f in findings], open(args.json, 'w'), indent=1)
    if args.template and pending:
        known = {(e['key'], e['fingerprint']) for e in approvals}
        for f in pending:
            if (f['key'], f['fp']) not in known:
                approvals.append(dict(key=f['key'], status=f['status'], fingerprint=f['fp'],
                                      reviewer='', note=''))
        json.dump(approvals, open(args.approvals, 'w'), indent=2)
        open(args.approvals, 'a').write('\n')

    counts = {s: sum(f['status'] == s for f in findings) for s in order}
    print(', '.join(f'{n} {s}' for s, n in counts.items() if n))
    print(f'{len(pending)} unreviewed, {len(stale)} stale approvals; report: {args.report}')
    sys.exit(1 if pending else 0)


if __name__ == '__main__':
    main()
