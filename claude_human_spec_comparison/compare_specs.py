#!/usr/bin/env python3
"""Compare the human-written gold spec with the verified (Claude-written) spec of the same crate.

For each function that both specs give a contract, the script generates Verus obligations from
the two specs and runs Verus on them in a scratch copy of the verified crate.

  Claude => gold  Does the verified contract give everything the gold contract asks for?
                  A wrapper with the gold contract calls the verified function, so Verus checks
                  gold_pre ==> claude_pre (at the call) and
                  gold_pre && claude_post ==> gold_post (the wrapper's ensures).
  gold => Claude  Does the gold contract give everything the verified contract promises?
                  A wrapper with Claude's contract calls a stand-in that has the gold contract.

Usage:  python3 compare_specs.py VERUS_FIXED HUMAN_SPEC [--proofs FILE] [--report FILE]
                                 [--features F ...] [--invariant NAME] [--verus-arg ARG ...] [--keep]
  VERUS_FIXED  the verified crate (its root, or a folder that contains it, such as verus_fixed/)
  HUMAN_SPEC   the gold spec: a crate's source tree (its root, or a folder that contains it, such
               as verus_human_written_spec/), or a single .rs file
  --proofs and --report default to spec_proofs.rs and spec_comparison.md next to this script.

Which contracts are compared. In both specs, a contract is the `requires`/`ensures` of an exec
function inside `verus!`: a free function, an inherent method, or a trait method. A trait
method's contract is the trait declaration's clauses (for traits the crate defines) plus the
impl's. Functions that `macro_rules!` macros generate are found by expanding each invocation, and
only items whose `cfg` holds are used (--features; the host's pointer width; `verus_keep_ghost`).
Functions are matched by self type, trait and name; free functions by name. A function of the
verified crate that is outside `verus!` (or in a `#[verifier::external]` module) is trusted.

Conventions applied to the gold spec (each one is listed in the report):
  * gold definitions (spec fns, gold-only structs, ...) are copied into a module `gold_defs`, and
    gold contracts refer to them there, so they never mix with the verified crate's definitions of
    the same name; `closed` becomes `open`, since the comparison needs their bodies;
  * a copied gold definition keeps the meaning of the names it took from its own module: that
    module's items, and what the module imports from the crate, become absolute paths;
  * gold spec methods of an inherent impl (`impl T { spec fn m }`) are renamed `gold_m`, since a
    type's methods share one namespace, unless the verified crate defines `T::m` identically
    (mode, signature and body): then gold contracts mean the crate's `m`, as for same-named
    types and traits;
  * when a copied gold definition (an inherent spec method or a view) reads private fields of a
    verified type, those fields are `pub(crate)` in the scratch copy of the verified crate;
  * external specifications (`external_trait_specification`, `external_type_specification`,
    `external_fn_specification`, `assume_specification`), in either spec, specify items outside
    the crate: they are neither compared nor copied;
  * gold `View` impls become a `GoldView` trait (`x@` -> `x.gv()`);
  * with --invariant NAME, `x@.valid()` on NAME's argument type is read as the gold function NAME;
  * the gold spec's `broadcast axiom`s are in force;
  * an obligation whose gold contract mentions capacity is also checked with capacity removed,
    so that "differs only in capacity" is reported separately;
  * an obligation whose generated code does not compile (e.g. the two signatures differ) is
    reported as such, with the compiler's message, and the others are checked without it.

Proofs go in a separate file (--proofs), with these markers:
  * `proof fn` / `spec fn` items: lemmas, placed in the generated module;
  * `// @hint <obligation> before|after` followed by one `proof { }` block: inserted into that
    obligation's wrapper before or after the call it checks (`*`: every obligation);
  * `// @note <obligation>` followed by comment lines: an explanation shown next to a failure;
  * `// @interpret <name>`: the gold `uninterp spec fn <name>` is replaced by the `spec fn <name>`
    that the proofs file defines (a modeling choice; the report prints it);
  * `// @call <obligation> <expression>`: that obligation's wrapper calls the function as
    <expression>, for when the two signatures differ (a modeling choice; the report prints it).
The obligations themselves are generated from the specs on every run, so proofs cannot change
what is proved; the proofs file may not contain assume, admit, external_body, axioms or other
trusted constructs.

Exit status: 0 if every comparable obligation in the Claude => gold direction is proved (or
differs only in capacity, or has a note), 1 otherwise, 2 if the gold definitions or the proofs do
not compile or verify.
"""
import argparse
import collections
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PTR_WIDTH = struct.calcsize('P') * 8

# ------------------------------------------------------------------------------ tokens


TOKEN_RE = re.compile(r'''
    (?P<ws>\s+)
  | (?P<lcomment>//[^\n]*)
  | (?P<bcomment>/\*)
  | (?P<rawstr>b?r(?P<hashes>\#*)")
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])')
  | (?P<lifetime>'[A-Za-z_]\w*)
  | (?P<num>\d[\w]*(?:\.\d[\w]*)?(?:[eE][+-]?\d+)?)
  | (?P<ident>r\#[A-Za-z_]\w*|[A-Za-z_]\w*)
  | (?P<punct><==>|==>|<==|=~~=|=~=|===|!==|&&&|\|\|\||::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\*=|/=|%=|\^=|&=|\|=|\.\.=|\.\.\.|\.\.|[^\s])
''', re.VERBOSE | re.DOTALL)
IDENT_RE = re.compile(r'[A-Za-z_]\w*$')


class Tok:
    __slots__ = ('t', 's', 'e')

    def __init__(self, t, s, e):
        self.t, self.s, self.e = t, s, e

    def __repr__(self):
        return self.t


def tokenize(text):
    """Tokens of Rust/Verus source, without whitespace and comments."""
    toks, i = [], 0
    while i < len(text):
        m = TOKEN_RE.match(text, i)
        kind = m.lastgroup
        if kind == 'bcomment':
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
            toks.append(Tok(text[i:end], i, end))
            i = end
            continue
        if kind not in ('ws', 'lcomment', 'hashes'):
            toks.append(Tok(m.group(), i, m.end()))
        i = m.end()
    return toks


OPEN, CLOSE = '([{', ')]}'


def tt(x):
    return x.t if isinstance(x, Tok) else x


def match_close(toks, i):
    """Index of the bracket closing toks[i] (one of `([{`)."""
    depth = 0
    for j in range(i, len(toks)):
        t = tt(toks[j])
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced brackets')


def match_angle(toks, i):
    """Index of the `>` closing the `<` at toks[i] (in generics; `->` is one token)."""
    depth = 0
    for j in range(i, len(toks)):
        t = tt(toks[j])
        if t == '<':
            depth += 1
        elif t == '>':
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced generics')


def text_of(src, toks, a, b):
    """Source text of toks[a..=b]."""
    return src[toks[a].s:toks[b].e]


def line_indent(src, offset):
    start = src.rfind('\n', 0, offset) + 1
    return len(src[start:offset]) - len(src[start:offset].lstrip(' ')), src[start:offset].strip() == ''


def strs(toks):
    """Token strings of Toks, with two `<` (or two `>`) that touch in the source glued back into
    `<<` (`>>`). The tokenizer keeps them apart, for generics; glued, they also read as shifts,
    and Rust splits them again in generics."""
    out = []
    for k, t in enumerate(toks):
        if out and t.t in ('<', '>') and out[-1] == t.t and toks[k - 1].e == t.s:
            out[-1] += t.t
        else:
            out.append(t.t)
    return out


def retok(s):
    return strs(tokenize(s))

# ------------------------------------------------------------------------------- items

ITEM_KINDS = {'fn', 'struct', 'enum', 'union', 'trait', 'impl', 'mod', 'use', 'type', 'const',
              'static', 'extern', 'macro_rules', 'broadcast_use', 'broadcast_group',
              'assume_specification'}
MODIFIERS = {'pub', 'const', 'unsafe', 'async', 'open', 'closed', 'spec', 'proof', 'exec',
             'uninterp', 'broadcast', 'axiom', 'tracked', 'ghost', 'default'}
SPEC_MODS = {'spec', 'proof', 'uninterp', 'axiom', 'open', 'closed'}
CLAUSE_KWS = {'requires', 'ensures', 'recommends', 'decreases', 'opens_invariants', 'no_unwind',
              'returns', 'invariant'}


class Item:
    def __init__(self, **kw):
        self.__dict__.update(kw)


def parse_items(src, toks, lo, hi):
    """Items in toks[lo:hi]: kind, token span, modifiers, body span and (for impls and traits)
    members. A macro invocation `name!(..)` is an item of kind `macro_call`."""
    items, i = [], lo
    while i < hi:
        start = i
        while i < hi and toks[i].t == '#':
            j = i + 1 + (toks[i + 1].t == '!')
            i = match_close(toks, j) + 1
        if i >= hi:
            break
        if toks[i].t == ';':
            i += 1
            continue
        mods, vis = [], None
        if toks[i].t == 'pub':
            vis = i
            i += 1
            if toks[i].t == '(':
                i = match_close(toks, i) + 1
        while toks[i].t in MODIFIERS:
            if toks[i].t == 'const' and toks[i + 1].t not in ('fn', 'unsafe', 'extern'):
                break
            if toks[i].t == 'broadcast' and toks[i + 1].t in ('use', 'group'):
                break
            mods.append(toks[i].t)
            i += 1
            if mods[-1] in ('open', 'closed') and toks[i].t == '(':  # `open(crate) spec fn`
                i = match_close(toks, i) + 1
        if toks[i].t == 'extern' and toks[i + 1].t.startswith('"'):
            i += 2
        kw = i
        kind = toks[i].t
        if kind == 'broadcast':
            kind = 'broadcast_' + toks[i + 1].t
        if kind not in ITEM_KINDS and IDENT_RE.match(kind) and toks[i + 1].t == '!' and toks[i + 2].t in OPEN:
            end = match_close(toks, i + 2)
            if end + 1 < hi and toks[end + 1].t == ';':
                end += 1
            items.append(Item(kind='macro_call', start=start, kw=kw, vis=vis, mods=mods, body=None,
                              members=[], end=end))
            i = end + 1
            continue
        if kind not in ITEM_KINDS:
            raise ValueError(f'unexpected token {kind!r} at offset {toks[i].s}')
        item = Item(kind=kind, start=start, kw=kw, vis=vis, mods=mods, body=None, members=[])
        if kind == 'fn':
            indent, _ = line_indent(src, toks[start].s)
            k, saw_clause = kw + 1, False
            while True:
                t = toks[k].t
                if t == '{':
                    col, alone = line_indent(src, toks[k].s)
                    if not saw_clause or (alone and col == indent):
                        item.body = (k, match_close(toks, k))
                        item.end = item.body[1]
                        break
                    k = match_close(toks, k) + 1
                    continue
                if t in '([':
                    k = match_close(toks, k) + 1
                    continue
                if t == ';':
                    item.end = k
                    break
                if t in CLAUSE_KWS and toks[k - 1].t != '.':
                    saw_clause = True
                k += 1
        elif kind in ('impl', 'trait', 'struct', 'enum', 'union', 'mod', 'broadcast_group'):
            k = kw + 1
            while toks[k].t not in ('{', ';'):
                k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
            if toks[k].t == ';':
                item.end = k
            else:
                item.body = (k, match_close(toks, k))
                item.end = item.body[1]
                if kind in ('impl', 'trait'):
                    item.members = parse_items(src, toks, k + 1, item.body[1])
        elif kind == 'macro_rules':
            item.end = match_close(toks, kw + 3)
        elif kind in ('const', 'static'):  # `exec static X: T ensures .. { .. }` has no `=` or `;`
            k, saw_eq = kw, False
            while True:
                t = toks[k].t
                if t == ';':
                    break
                if t == '=':
                    saw_eq = True
                if t == '{' and not saw_eq:
                    k = match_close(toks, k)
                    break
                k = match_close(toks, k) + 1 if t in OPEN else k + 1
            item.end = k
        else:  # use, type, extern crate, broadcast use, ...
            k = kw
            while toks[k].t != ';':
                k = match_close(toks, k) + 1 if toks[k].t in OPEN else k + 1
            item.end = k
        items.append(item)
        i = item.end + 1
    return items


def vis_of(toks, i):
    """Visibility of an item whose `pub` (if any) is toks[i]: `pub`, `pub(crate)`, `pub(super)`,
    `pub(incrate)` (tokens joined), or '' (private)."""
    if i is None or toks[i].t != 'pub':
        return ''
    if toks[i + 1].t == '(':
        return ''.join(t.t for t in toks[i:match_close(toks, i + 1) + 1])
    return 'pub'


# items that specify something outside the crate (std, ...): they are neither compared nor copied
EXTERNAL_SPEC = re.compile(r'verifier\s*::\s*external_(?:trait|type|fn)_specification')


def attr_spans(toks, a, b):
    """The `#[..]` / `#![..]` attributes in toks[a:b], as (start, end) index pairs."""
    spans, i = [], a
    while i < b:
        if toks[i].t == '#':
            j = i + 1 + (toks[i + 1].t == '!')
            e = match_close(toks, j)
            spans.append((i, e))
            i = e + 1
        else:
            i += 1
    return spans

# ------------------------------------------------------------------------------- cfg


def split_commas(ts):
    parts, cur, depth = [], [], 0
    for t in ts:
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
        if t == ',' and depth == 0:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        parts.append(cur)
    return parts


def eval_cfg(ts, features):
    """Value of a cfg predicate (token strings): all/any/not, `feature = ".."`,
    `target_pointer_width = ".."` (the host's), and `verus_keep_ghost` (true). Others: false."""
    if not ts:
        return True
    name = ts[0]
    if len(ts) > 1 and ts[1] == '(':
        args = [eval_cfg(p, features) for p in split_commas(ts[2:match_close(ts, 1)])]
        return {'all': all(args), 'any': any(args), 'not': not args[0] if args else True}.get(name, False)
    if len(ts) > 2 and ts[1] == '=':
        value = ts[2].strip('"')
        if name == 'feature':
            return value in features
        if name == 'target_pointer_width':
            return value == str(PTR_WIDTH)
        return False
    return name == 'verus_keep_ghost'


def cfg_holds(toks, spans, features):
    for a, e in spans:
        j = a + 1 + (toks[a + 1].t == '!')
        if toks[j + 1].t == 'cfg' and toks[j + 2].t == '(':
            if not eval_cfg([t.t for t in toks[j + 3:match_close(toks, j + 2)]], features):
                return False
    return True

# --------------------------------------------------------------------------- signatures


# tokens after which a `|` opens the parameters of a closure or quantifier (else it is a bitwise or)
BINDER_BEFORE = {None, 'forall', 'exists', 'choose', 'move', '(', '[', '{', ',', '=', '!', '=>', '==>',
                 '<==', '<==>', '&&', '||', '&&&', '|||', 'return', ':'}


def split_top(toks, lo, hi, angle=False):
    """Split toks[lo:hi] at top-level commas (not inside brackets, generics or `|..|` binders)."""
    parts, cur, depth, adepth, binder, prev = [], [], 0, 0, False, None
    for t in toks[lo:hi]:
        s = t.t
        if s in OPEN:
            depth += 1
        elif s in CLOSE:
            depth -= 1
        elif angle and s == '<':
            adepth += 1
        elif angle and s == '>':
            adepth -= 1
        elif s == '|' and depth == 0 and (binder or prev in BINDER_BEFORE):
            binder = not binder  # `|x, y|` of a closure or quantifier (not a bitwise `|`)
        prev = s
        if s == ',' and depth == 0 and adepth == 0 and not binder:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        parts.append(cur)
    return parts


class Sig:
    pass


def parse_sig(src, toks, item):
    """Name, generics, receiver, params, return, where and clauses of a fn item."""
    sg = Sig()
    k = item.kw + 1
    sg.name = toks[k].t
    k += 1
    sg.generics = ''
    if toks[k].t == '<':
        e = match_angle(toks, k)
        sg.generics = text_of(src, toks, k + 1, e - 1)
        k = e + 1
    pe = match_close(toks, k)
    params = split_top(toks, k + 1, pe, angle=True)
    sg.receiver, sg.recv_lt, sg.params = None, '', []
    for p in params:
        ts = [t.t for t in p]
        if 'self' in ts and ':' not in ts:
            sg.recv_lt = ts[1] if len(ts) > 1 and ts[0] == '&' and ts[1].startswith("'") else ''
            sg.receiver = '&mut' if ts[:2] == ['&', 'mut'] or (len(ts) > 2 and ts[0] == '&' and ts[2] == 'mut') \
                else '&' if ts[0] == '&' else 'self'
            continue
        colon = ts.index(':')
        sg.params.append((''.join(ts[:colon]).replace('mut', ''), text_of(src, p, colon + 1, len(p) - 1)))
    k = pe + 1
    sg.ret_name = sg.ret_type = None
    end = item.body[0] if item.body else item.end
    if toks[k].t == '->':
        k += 1
        if toks[k].t == '(' and toks[k + 1].t not in ('(', ')') and toks[k + 2].t == ':':
            e = match_close(toks, k)
            sg.ret_name = toks[k + 1].t
            sg.ret_type = text_of(src, toks, k + 3, e - 1)
            k = e + 1
        else:
            a, depth = k, 0
            while k < end and not (depth == 0 and toks[k].t in CLAUSE_KWS | {'where'}):
                depth += toks[k].t == '<'
                depth -= toks[k].t == '>'
                k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
            sg.ret_type = text_of(src, toks, a, k - 1)
    sg.where = ''
    if toks[k].t == 'where':
        a = k + 1
        while k < end and not (toks[k].t in CLAUSE_KWS and toks[k - 1].t != '.'):
            k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
        sg.where = text_of(src, toks, a, k - 1).rstrip(',')
    sg.clauses = {}
    is_kw = lambda k: toks[k].t in CLAUSE_KWS and toks[k - 1].t != '.'  # not `f.requires(..)`
    while k < end:
        if is_kw(k):
            kwd, a = toks[k].t, k + 1
            k += 1
            while k < end and not is_kw(k):
                k = match_close(toks, k) + 1 if toks[k].t in OPEN else k + 1
            sg.clauses[kwd] = [c for c in split_top(toks, a, k) if c]
        else:
            k += 1
    return sg


def impl_parts(src, toks, item):
    """(generics text, trait text or None, self type text) of an impl item."""
    k = item.kw + 1
    gen = ''
    if toks[k].t == '<':
        e = match_angle(toks, k)
        gen = text_of(src, toks, k + 1, e - 1)
        k = e + 1
    head_end = item.body[0]
    w = next((j for j in range(k, head_end) if toks[j].t == 'where'), head_end)
    f = None
    depth = 0
    for j in range(k, w):
        depth += toks[j].t == '<'
        depth -= toks[j].t == '>'
        if toks[j].t == 'for' and depth == 0:
            f = j
    if f is None:
        return gen, None, text_of(src, toks, k, w - 1)
    return gen, text_of(src, toks, k, f - 1), text_of(src, toks, f + 1, w - 1)


def impl_where(src, toks, item):
    """The `where` clause of an impl item's header (without `where`), or ''."""
    head_end = item.body[0]
    w = next((j for j in range(item.kw + 1, head_end) if toks[j].t == 'where'), None)
    return text_of(src, toks, w + 1, head_end - 1).rstrip(',') if w is not None and w + 1 < head_end else ''


def core_type(ty):
    """`&'a mut crate::Slab<T>` -> ('&mut', 'Slab')."""
    ts = [t.t for t in tokenize(ty or '')]
    prefix = ''
    while ts and ts[0] in ('&', 'mut') or (ts and ts[0].startswith("'")):
        if ts[0] == '&':
            prefix += '&'
        elif ts[0] == 'mut':
            prefix += 'mut '
        ts = ts[1:]
    name = ''
    depth = 0
    for t in ts:
        if t == '<':
            depth += 1
        elif t == '>':
            depth -= 1
        elif depth == 0 and IDENT_RE.match(t):
            name = t
    return prefix.strip(), name


def fn_key(self_ty, trait, name):
    pre, base = core_type(self_ty)
    tr = core_type(trait)[1] if trait else ''
    return ((pre + ' ' if pre else '') + base, tr, name)

# ------------------------------------------------------------------------- macro_rules


def bind(pattern, args, text):
    """Bind the metavariables of a `macro_rules!` arm's pattern (token strings) to the text of an
    invocation's arguments (Toks into `text`). None if the arm does not match. Handles `$x:frag`
    and literal tokens; repetitions `$(...)*` are not supported."""
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
            if j >= len(args) or args[j].t != e[1]:
                return None
            j += 1
        elif e[2] in ('ident', 'literal', 'lifetime', 'tt'):
            if j >= len(args):
                return None
            out[e[1]] = text[args[j].s:args[j].e]
            j += 1
        else:  # ty, expr, path, pat, ...: everything up to the next literal token of the pattern
            stop = next((x[1] for x in elems[n + 1:] if x[0] == 'lit'), None)
            start, depth = j, 0
            while j < len(args) and not (depth == 0 and args[j].t == stop):
                depth += (args[j].t in OPEN) - (args[j].t in CLOSE)
                j += 1
            if j == start:
                return None
            out[e[1]] = text[args[start].s:args[j - 1].e]
    return out if j == len(args) else None

# ----------------------------------------------------------------------- reading a spec


class Doc:
    """A piece of source: a file, or the body of a macro invocation with its arguments in."""

    def __init__(self, label, text, mp):
        self.label, self.text, self.mp, self.toks = label, text, mp, tokenize(text)


def crate_files(root):
    """{module path: (relative path, text)} of a crate source tree, or of a single file."""
    if os.path.isfile(root):
        return {(): (os.path.basename(root), open(root).read())}
    src = os.path.join(root, 'src')
    out = {}
    for dirpath, _, names in os.walk(src):
        for n in sorted(names):
            if not n.endswith('.rs'):
                continue
            path = os.path.join(dirpath, n)
            parts = os.path.relpath(path, src)[:-3].split(os.sep)
            if parts in (['lib'], ['main']):
                mp = ()
            elif parts[-1] == 'mod':
                mp = tuple(parts[:-1])
            else:
                mp = tuple(parts)
            out[mp] = (os.path.relpath(path, root), open(path).read())
    return out


class Source:
    """The items of a crate (or a gold spec file) that the comparison needs."""

    def __init__(self, root, features):
        self.features = features
        self.fns = collections.defaultdict(list)  # key -> [function record] (verified, with contract or not)
        self.trusted = set()                      # keys of functions outside `verus!`
        self.traits = {}                          # trait name -> record
        self.defs = []                            # spec-level items (copied for the gold side)
        self.inherent_spec = set()                # (type, method) of spec methods of inherent impls
        self.inherent_bodies = {}                 # (type, method) -> mode, signature and body tokens
        self.views, self.model_fields = {}, {}
        self.mod_items = collections.defaultdict(set)
        self.imports = collections.defaultdict(list)
        self.field_types, self.structs, self.names = {}, set(), set()
        self.trusted_types = set()
        self.uninterp, self.axioms, self.axiom_covered = set(), [], set()
        self.external_mods, self.warnings, self.macros = set(), [], {}
        self.mod_vis, self.item_vis = {}, {}      # module path -> visibility; (module path, name) -> visibility
        self.external_specs = []                  # external specifications (neither compared nor copied)
        files = crate_files(root)
        docs = []
        for mp, (rel, text) in sorted(files.items(), key=lambda kv: (len(kv[0]), kv[0])):
            toks = tokenize(text)
            blank = list(text)
            for k in range(len(toks) - 3):
                if toks[k].t != 'macro_rules' or toks[k + 1].t != '!' or toks[k + 3].t not in OPEN:
                    continue
                arms, a = [], k + 4
                close = match_close(toks, k + 3)
                while a < close and toks[a].t in OPEN:
                    p_close = match_close(toks, a)
                    b_open = p_close + 2  # after `=>`
                    b_close = match_close(toks, b_open)
                    arms.append(([t.t for t in toks[a + 1:p_close]], toks[b_open].e, toks[b_close].s))
                    a = b_close + 1 + (b_close + 1 < close and toks[b_close + 1].t == ';')
                self.macros[toks[k + 2].t] = (text, arms)
                for _, lo, hi in arms:  # bodies are read only through their invocations
                    for x in range(lo, hi):
                        if blank[x] != '\n':
                            blank[x] = ' '
            docs.append(Doc(rel, ''.join(blank), mp))
        for d in docs:
            ext = any(d.mp[:len(e)] == e for e in self.external_mods)
            self.walk(d, 0, len(d.toks), d.mp, ext)
        # which viewed types are placeholders: their view uses an uninterpreted function no axiom covers
        self.placeholder_types = set()

    def cfg_ok(self, doc, a, b):
        return cfg_holds(doc.toks, attr_spans(doc.toks, a, b), self.features)

    def walk(self, doc, lo, hi, mp, ext, depth=0):
        """Items outside `verus!`: modules, imports, macro invocations; `verus!` blocks are read
        with `collect`."""
        toks, i = doc.toks, lo
        while i < hi:
            a0 = i
            while i < hi and toks[i].t == '#':
                i = match_close(toks, i + 1 + (toks[i + 1].t == '!')) + 1
            if i >= hi:
                break
            t = toks[i].t
            if t == ';':
                i += 1
                continue
            if t == 'verus' and i + 2 < hi and toks[i + 1].t == '!' and toks[i + 2].t == '{':
                c = match_close(toks, i + 2)
                self.collect(doc, i + 3, c, mp, ext, depth)
                i = c + 1
                continue
            j = i
            if toks[j].t == 'pub':
                j += 1
                if toks[j].t == '(':
                    j = match_close(toks, j) + 1
            kw = toks[j].t
            ok = self.cfg_ok(doc, a0, i)
            if kw == 'mod' and ok:
                self.mod_vis[mp + (toks[j + 1].t,)] = vis_of(toks, i)
            if kw == 'mod' and toks[j + 2].t == '{':
                c = match_close(toks, j + 2)
                if ok:
                    self.mod_items[mp].add(toks[j + 1].t)
                    self.walk(doc, j + 3, c, mp + (toks[j + 1].t,), ext, depth)
                i = c + 1
                continue
            if kw == 'mod':
                if ok:
                    self.mod_items[mp].add(toks[j + 1].t)
                    if re.search(r'verifier\s*::\s*external\s*[\],)]', doc.text[toks[a0].s:toks[i].s]):
                        self.external_mods.add(mp + (toks[j + 1].t,))
                i = j + 3
                continue
            if kw == 'use':
                e = j
                while toks[e].t != ';':
                    e = match_close(toks, e) + 1 if toks[e].t in OPEN else e + 1
                if ok:
                    self.imports[mp].append((doc, j, e))
                i = e + 1
                continue
            if kw == 'macro_rules':
                i = match_close(toks, j + 3) + 1
                continue
            if IDENT_RE.match(kw) and toks[j + 1].t == '!' and toks[j + 2].t in OPEN:
                c = match_close(toks, j + 2)
                if ok:
                    self.expand(doc, j, c, mp, ext, False, depth)
                i = c + 1
                continue
            # any other item outside `verus!` is not verified
            k = j
            while k < hi:
                if toks[k].t == ';':
                    break
                if toks[k].t == '{':
                    k = match_close(toks, k)
                    break
                k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
            if ok:
                try:
                    for it in parse_items(doc.text, toks, a0, min(k, hi - 1) + 1):
                        self.unverified(doc, it, mp)
                except (ValueError, IndexError):
                    pass
            i = k + 1

    def unverified(self, doc, it, mp):
        toks = doc.toks
        if it.kind in ('struct', 'enum', 'union'):
            self.trusted_types.add(toks[it.kw + 1].t)
            self.structs.add(toks[it.kw + 1].t)
        if it.kind not in ('impl', 'use', 'macro_call', 'macro_rules', 'broadcast_use', 'assume_specification'):
            self.names.add(toks[it.kw + 1].t)
            self.mod_items[mp].add(toks[it.kw + 1].t)
            self.item_vis[(mp, toks[it.kw + 1].t)] = vis_of(toks, it.vis)
        if it.kind == 'fn':
            self.trusted.add(('', '', toks[it.kw + 1].t))
        if it.kind == 'impl':
            gen, trait, self_ty = impl_parts(doc.text, toks, it)
            for m in it.members:
                if m.kind == 'fn':
                    self.trusted.add(fn_key(self_ty, trait, toks[m.kw + 1].t))

    def expand(self, doc, j, c, mp, ext, in_verus, depth):
        name = doc.toks[j].t
        if name not in self.macros or depth > 8:
            return
        mtext, arms = self.macros[name]
        args = doc.toks[j + 3:c]
        for pattern, lo, hi in arms:
            b = bind(pattern, args, doc.text)
            if b is None:
                continue
            body = re.sub(r'\$(\w+)', lambda m: b.get(m.group(1), m.group(0)).replace('\n', ' '), mtext[lo:hi])
            sub = Doc(f'{doc.label}: {name}!({doc.text[args[0].s:args[-1].e] if args else ""})', body, mp)
            if in_verus:
                self.collect(sub, 0, len(sub.toks), mp, ext, depth + 1)
            else:
                self.walk(sub, 0, len(sub.toks), mp, ext, depth + 1)
            return
        self.warnings.append(f'{doc.label}: no arm of `{name}!` matches its arguments')

    def collect(self, doc, lo, hi, mp, ext, depth=0):
        """Items inside a `verus!` block."""
        try:
            items = parse_items(doc.text, doc.toks, lo, hi)
        except (ValueError, IndexError) as e:
            self.warnings.append(f'{doc.label}: a `verus!` block could not be read ({e}); skipped')
            return
        for it in items:
            self.item(doc, it, mp, ext, depth)

    def item(self, doc, it, mp, ext, depth):
        toks = doc.toks
        if not self.cfg_ok(doc, it.start, it.kw):
            return
        kind = it.kind
        if kind == 'macro_call':
            close = match_close(toks, it.kw + 2)
            if toks[it.kw].t == 'verus':  # a `verus!` block inside verified code (from a macro)
                self.collect(doc, it.kw + 3, close, mp, ext, depth)
            else:
                self.expand(doc, it.kw, close, mp, ext, True, depth)
            return
        if kind == 'use':
            self.imports[mp].append((doc, it.kw, it.end))
            return
        if kind == 'assume_specification' or EXTERNAL_SPEC.search(doc.text[toks[it.start].s:toks[it.kw].s]):
            self.external_specs.append(' '.join(doc.text[toks[it.kw].s:toks[it.end].e].split())[:80])
            return
        if kind in ('impl', 'broadcast_use', 'macro_rules'):
            name = None
        else:
            name = toks[it.kw + 1 + (kind == 'broadcast_group')].t
            self.names.add(name)
            self.mod_items[mp].add(name)
            self.item_vis[(mp, name)] = vis_of(toks, it.vis)
        if kind == 'mod':
            self.mod_vis[mp + (name,)] = vis_of(toks, it.vis)
            if it.body:
                self.collect(doc, it.body[0] + 1, it.body[1], mp + (name,), ext, depth)
            return
        if kind == 'fn':
            if set(it.mods) & SPEC_MODS:
                if 'uninterp' in it.mods:
                    self.uninterp.add(name)
                if 'axiom' in it.mods and 'broadcast' in it.mods:
                    self.axioms.append(name)
                    for j in range(it.kw, it.end):
                        if toks[j].t == '#' and toks[j + 2].t == 'trigger':
                            self.axiom_covered.add(toks[j + 4].t)
                self.defs.append(Item(doc=doc, it=it, mp=mp, kind='fn'))
            else:
                self.add_fn(doc, it, mp, ext, None, None, '', '')
            return
        if kind in ('struct', 'enum', 'union'):
            self.structs.add(name)
            if kind == 'struct' and it.body:
                for f in split_top(toks, it.body[0] + 1, it.body[1], angle=True):
                    ts = [t.t for t in f]
                    if ':' in ts:
                        self.field_types[(name, ts[ts.index(':') - 1])] = core_type(
                            text_of(doc.text, f, ts.index(':') + 1, len(f) - 1))[1]
            self.defs.append(Item(doc=doc, it=it, mp=mp, kind=kind))
            return
        if kind == 'trait':
            rec = Item(name=name, mp=mp, doc=doc, it=it, assoc=set(), methods={}, vis=vis_of(toks, it.vis))
            for m in it.members:
                if m.kind in ('type', 'const', 'fn'):
                    rec.assoc.add(toks[m.kw + 1].t)
                if m.kind == 'fn' and not set(m.mods) & SPEC_MODS:
                    rec.methods[toks[m.kw + 1].t] = Item(doc=doc, it=m, sig=parse_sig(doc.text, toks, m), mp=mp)
            self.traits[name] = rec
            self.defs.append(Item(doc=doc, it=it, mp=mp, kind='trait'))
            return
        if kind == 'impl':
            gen, trait, self_ty = impl_parts(doc.text, toks, it)
            tcore = core_type(trait)[1] if trait else None
            if tcore == 'View':
                self.views[core_type(self_ty)[1]] = Item(doc=doc, it=it)
                self.defs.append(Item(doc=doc, it=it, mp=mp, kind='view'))
                return
            spec_members = [m for m in it.members if m.kind == 'fn' and set(m.mods) & SPEC_MODS]
            if not trait and spec_members:
                for m in spec_members:
                    self.inherent_spec.add((core_type(self_ty)[1], toks[m.kw + 1].t))
                    self.inherent_bodies[(core_type(self_ty)[1], toks[m.kw + 1].t)] = tuple(
                        [x for x in m.mods if x in ('spec', 'proof')] + strs(toks[m.kw:m.end + 1]))
                self.defs.append(Item(doc=doc, it=it, mp=mp, kind='inherent', members=spec_members,
                                      self_ty=self_ty, gen=gen))
            where = impl_where(doc.text, toks, it)
            for m in it.members:
                if m.kind == 'fn' and not set(m.mods) & SPEC_MODS and self.cfg_ok(doc, m.start, m.kw):
                    self.add_fn(doc, m, mp, ext, self_ty, trait, gen, where)
            return
        if kind in ('const', 'static', 'type', 'broadcast_group'):
            self.defs.append(Item(doc=doc, it=it, mp=mp, kind=kind))

    def add_fn(self, doc, m, mp, ext, self_ty, trait, gen, impl_where_):
        sig = parse_sig(doc.text, doc.toks, m)
        key = fn_key(self_ty, trait, sig.name) if self_ty else ('', '', sig.name)
        if ext:
            self.trusted.add(key)
            return
        attrs = doc.text[doc.toks[m.start].s:doc.toks[m.kw].s]
        self.fns[key].append(Item(key=key, doc=doc, it=m, sig=sig, mp=mp, self_ty=self_ty, trait=trait,
                                  gen=gen, impl_where=impl_where_, unsafe='unsafe' in m.mods,
                                  external_body=bool(re.search(r'verifier\s*::\s*external_body', attrs))))

    def finish(self):
        """Placeholders and model fields, once every item is known."""
        self.placeholder_types = set()
        for name, v in self.views.items():
            used = {v.doc.toks[j].t for j in range(v.it.start, v.it.end)} & self.uninterp
            if used - self.axiom_covered:
                self.placeholder_types.add(name)
        structs = {d.doc.toks[d.it.kw + 1].t: d for d in self.defs if d.kind == 'struct' and d.it.body}
        for name, v in self.views.items():
            toks = v.doc.toks
            j = next((j for j in range(v.it.start, v.it.end) if toks[j].t == 'type' and toks[j + 1].t == 'V'), None)
            st = structs.get(toks[j + 3].t) if j is not None else None
            if st:
                lo, hi = st.it.body
                st_toks = st.doc.toks
                self.model_fields[name] = [st_toks[k].t for k in range(lo + 1, hi)
                                           if st_toks[k + 1].t == ':' and st_toks[k - 1].t in ('{', ',', 'pub', ')')]

    def visible_at_root(self, mp, name=None):
        """Whether the module `crate::<mp>` (and, given `name`, its item `name`) can be named from a
        module at the crate root, such as the generated `gold_check`. Unknown visibility (an item
        that a macro or a re-export provides) counts as visible."""
        def ok(vis, decl_mp):  # an item declared in module `decl_mp`
            return (not decl_mp or vis in ('pub', 'pub(crate)', 'pub(incrate)')
                    or (vis == 'pub(super)' and len(decl_mp) == 1))
        for i in range(1, len(mp)):
            v = self.mod_vis.get(mp[:i + 1])
            if v is not None and not ok(v, mp[:i]):
                return False
        v = self.item_vis.get((mp, name)) if name is not None else None
        return v is None or ok(v, mp)

    def path_visible(self, segs):
        """`visible_at_root` for an absolute path (`crate`, then module and item names)."""
        segs = tuple(segs[1:]) if segs and segs[0] == 'crate' else tuple(segs)
        if not segs or segs in self.mod_vis:
            return self.visible_at_root(segs)
        return self.visible_at_root(segs[:-1], segs[-1])

    def trait_path(self, name):
        rec = self.traits.get(name)
        return '::'.join(('crate',) + rec.mp + (name,)) if rec else None

    def contract(self, rec):
        """(requires, ensures) of a function record: the trait declaration's clauses (traits of
        this crate), renamed to the impl's parameters, then the function's own. Each clause is
        (tokens, original text, module path, renames)."""
        req, ens = [], []
        tdecl = self.traits.get(core_type(rec.trait)[1]).methods.get(rec.sig.name) \
            if rec.trait and core_type(rec.trait)[1] in self.traits else None
        orig = lambda doc, c: ' '.join(doc.text[c[0].s:c[-1].e].split())
        if tdecl:
            ren = {a: b for (a, _), (b, _) in zip(tdecl.sig.params, rec.sig.params) if a != b}
            if tdecl.sig.ret_name and tdecl.sig.ret_name != (rec.sig.ret_name or 'ret'):
                ren[tdecl.sig.ret_name] = rec.sig.ret_name or 'ret'  # (`side_sig` names it `ret`)
            for c in tdecl.sig.clauses.get('requires', []):
                req.append((strs(c), orig(tdecl.doc, c), tdecl.mp, ren))
            for c in tdecl.sig.clauses.get('ensures', []):
                ens.append((strs(c), orig(tdecl.doc, c), tdecl.mp, ren))
        for c in rec.sig.clauses.get('requires', []):
            req.append((strs(c), orig(rec.doc, c), rec.mp, {}))
        for c in rec.sig.clauses.get('ensures', []):
            ens.append((strs(c), orig(rec.doc, c), rec.mp, {}))
        return req, ens

# ---------------------------------------------------------------------------- imports


def flatten_use(doc, a, b, mp, mod_items):
    """Import lines (`use path;`, `use path as x;`, `use path::*;`) of the `use` item at
    toks[a..b], with paths made absolute (`crate::..`)."""
    ts = [t.t for t in doc.toks[a + 1:b]]

    def walk(ts, prefix):
        out, k, path = [], 0, list(prefix)
        while k < len(ts):
            t = ts[k]
            if t == '::':
                k += 1
            elif t == '{':
                e = match_close(ts, k)
                for part in split_commas(ts[k + 1:e]):
                    out += walk(part, path)
                return out
            elif t == '*':
                out.append((path, None, True))
                return out
            elif t == 'as':
                out.append((path, ts[k + 1], False))
                return out
            else:
                path.append(t)
                k += 1
        if path:
            if path[-1] == 'self':
                path = path[:-1]
            out.append((path, None, False))
        return out

    lines = []
    for path, alias, glob in walk(ts, []):
        if not path:
            continue
        if path[0] == 'self':
            path = ['crate', *mp, *path[1:]]
        elif path[0] == 'super':
            up = list(mp)
            while path and path[0] == 'super':
                up, path = up[:-1], path[1:]
            path = ['crate', *up, *path]
        elif path[0] != 'crate' and path[0] in mod_items.get(mp, ()):
            path = ['crate', *mp, *path]
        p = '::'.join(path)
        name = alias or ('*' if glob else path[-1])
        lines.append((name, f'use {p}::*;' if glob else (f'use {p} as {alias};' if alias else f'use {p};'),
                      path[0], path))
    return lines


def import_block(src, mps, local_only=False):
    """The import lines of the modules `mps` of `src`, one per imported name."""
    seen, out = set(), []
    for mp in mps:
        for doc, a, b in src.imports.get(mp, []):
            for name, line, root, path in flatten_use(doc, a, b, mp, src.mod_items):
                if local_only and root in ('crate', 'self', 'super'):
                    continue
                if root == 'crate' and not src.path_visible(path):
                    continue  # private to its module: the generated module cannot import it
                key = line if name == '*' else name
                if key not in seen:
                    seen.add(key)
                    out.append(line)
    return out

# ---------------------------------------------------------------------------- rewriting


def expr_before(ts, i):
    """Start index of the postfix expression that ends at ts[i-1] (e.g. `old(self)`, `self.slab`)."""
    j = i - 1
    while j >= 0:
        if ts[j] == ')':
            depth = 0
            while True:
                depth += ts[j] == ')'
                depth -= ts[j] == '('
                if depth == 0:
                    break
                j -= 1
            if j > 0 and IDENT_RE.match(ts[j - 1]):
                j -= 1
        if j > 1 and ts[j - 1] == '.':
            j -= 2
            continue
        if j > 0 and ts[j - 1] == '*':
            j -= 1
        return j
    return 0


def expr_type(ts, a, b, env, field_types):
    """Core type of ts[a:b] (`slf`, `old(slf)`, `final(slf)`, `slf.slab`, a param, ...), or None."""
    e = [t for t in ts[a:b] if t not in ('*', '(', ')', 'old', 'final')]
    if not e or e[0] not in env:
        return None
    ty = env[e[0]]
    for k in range(1, len(e) - 1, 2):
        if e[k] != '.':
            return None
        ty = field_types.get((ty, e[k + 1]))
        if ty is None:
            return None
    return ty


def expr_after(ts, i):
    """End index (exclusive) of the operand of a binary `==` that starts at ts[i]."""
    stop = {',', ';', '&&', '||', '&&&', '|||', '==>', '<==>', '<==', '=>', '==', '!=', '===', '!=='}
    depth, j = 0, i
    while j < len(ts):
        t = ts[j]
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and t in stop:
            break
        j += 1
    return j


def binders(ts):
    """Names bound inside a clause: closure/quantifier parameters `|x: T, y|` and `let x`."""
    out, k = set(), 0
    while k < len(ts):
        if ts[k] == '|' and (k == 0 or ts[k - 1] in ('forall', 'exists', 'choose', '(', ',', '=', '!')):
            e = next((x for x in range(k + 1, len(ts)) if ts[x] == '|'), k)
            for x in range(k + 1, e):
                if IDENT_RE.match(ts[x]) and (x + 1 >= e or ts[x + 1] in (':', ',')):
                    out.add(ts[x])
            k = e + 1
            continue
        if ts[k] == 'let' and k + 1 < len(ts) and IDENT_RE.match(ts[k + 1]):
            out.add(ts[k + 1])
        k += 1
    return out


class Ctx:
    """How to rewrite clauses and types of one function, on one side (gold or Claude)."""

    def __init__(self, **kw):
        self.__dict__.update(kw)


def rewrite(ts, cx, renames=None, locals_=()):
    """Clause (or type) tokens -> tokens that mean the same in the generated module:
    the receiver is `slf`, `Self` is the self type (`Self::X` -> `<T as Trait>::X`), module-relative
    names are made absolute, and on the gold side gold definitions are `gold_defs::..`."""
    renames = renames or {}
    gold_side = cx.side == 'gold'
    local = set(locals_) | binders(ts) | set(renames.values())
    out, k = [], 0
    while k < len(ts):
        t = ts[k]
        prev = out[-1] if out else ''
        nxt = ts[k + 1] if k + 1 < len(ts) else ''
        if t in ('crate', 'super', 'self') and nxt == '::' and prev not in ('.', '::'):
            segs, j = [t], k
            while j + 2 < len(ts) and ts[j + 1] == '::' and IDENT_RE.match(ts[j + 2]):
                segs.append(ts[j + 2])
                j += 2
            up, rest = list(cx.mp), segs
            if rest[0] == 'self':
                rest = rest[1:]
            elif rest[0] == 'crate':
                up, rest = [], rest[1:]
            else:
                while rest and rest[0] == 'super':
                    up, rest = up[:-1], rest[1:]
            if gold_side and rest and rest[-1] in cx.gold_names:
                out += ['gold_defs', '::', rest[-1]]
            else:
                out += retok('::'.join(['crate'] + up + rest))
            k = j + 1
            continue
        if t == 'self' and nxt != '::':
            out.append('slf')
        elif t == 'Self':
            if nxt == '::' and k + 2 < len(ts) and cx.self_ty:
                x = ts[k + 2]
                tp = next((cx.verified.trait_path(tr) for tr in cx.self_traits
                           if tr in cx.verified.traits and x in cx.verified.traits[tr].assoc), None)
                out += retok(f'<{cx.self_ty} as {tp}>') if tp else retok(f'<{cx.self_ty}>')
            else:
                out += retok(cx.self_ty) if cx.self_ty else ['Self']
        elif t in renames and prev not in ('.', '::'):
            out.append(renames[t])
        elif IDENT_RE.match(t) and prev not in ('.', '::') and nxt != '!' and t not in local:
            if gold_side and t in cx.gold_names:
                out += ['gold_defs', '::', t]
            elif cx.mp and t in cx.src.mod_items.get(cx.mp, ()) and t not in cx.gold_names:
                out += retok('::'.join(('crate',) + cx.mp + (t,)))
            else:
                out.append(t)
        else:
            out.append(t)
        k += 1
    return out


def rewrite_contract(ts, cx, env, renames, nocap=False):
    """A contract clause in the generated module: `rewrite`, then (gold side) the view, invariant
    and renamed-method conventions."""
    ts = rewrite(ts, cx, renames, env.keys())
    if cx.side != 'gold':
        return ts
    gold, field_types = cx.gold, cx.verified.field_types
    # A model equality `x@ == y` is compared field by field (the same meaning, and each field then
    # gets Verus's automatic extensional equality); the capacity-free variant drops `capacity`.
    k = 0
    while k < len(ts):
        if ts[k] in ('==', '===') and k > 0 and ts[k - 1] == '@':
            a = expr_before(ts, k - 1)
            ty = expr_type(ts, a, k - 1, env, field_types)
            if ty in gold.model_fields and ty not in gold.placeholder_types:
                b = expr_after(ts, k + 1)
                x, y = ts[a:k - 1], ts[k + 1:b]
                new = ['(']
                for f in gold.model_fields[ty]:
                    if not (nocap and f == 'capacity'):
                        new += (['&&'] if len(new) > 1 else []) + x + ['@', '.', f, '==', '('] + y + [')', '.', f]
                new.append(')')
                ts = ts[:a] + new + ts[b:]
                k = a + len(new)
                continue
        k += 1
    out, k = [], 0
    while k < len(ts):  # x@.valid() -> x.gold_inv(); x@ -> x.gv(); x.m(..) -> x.gold_m(..)
        if ts[k] == '@':
            ty = expr_type(ts, expr_before(ts, k), k, env, field_types)
            if cx.inv_type and ty == cx.inv_type and ts[k + 1:k + 5] == ['.', 'valid', '(', ')']:
                out += ['.', 'gold_inv', '(', ')']
                k += 5
                continue
            if ty in gold.views:
                out += ['.', 'gv', '(', ')']
                k += 1
                continue
        if ts[k] == '.' and k + 2 < len(ts) and ts[k + 2] == '(':
            ty = expr_type(ts, expr_before(ts, k), k, env, field_types)
            if (ty, ts[k + 1]) in gold.inherent_spec:
                out += ['.', 'gold_' + ts[k + 1]]
                k += 2
                continue
        out.append(ts[k])
        k += 1
    return out


def rewrite_def_text(d, cx, gold):
    """Source of a gold definition for the module `gold_defs`: `pub(crate)` visibility, `open`
    for `closed`, `View` -> `GoldView`, `x@` -> `x.gv()` for viewed types, and the renamed
    inherent spec methods."""
    src, toks, item = d.doc.text, d.doc.toks, d.it
    edits = []
    env_by_fn = []
    field_types = cx.verified.field_types

    inherent = item.kind == 'impl' and not impl_parts(src, toks, item)[1]

    def visit(it, top):
        if it.vis is not None and toks[it.vis + 1].t != '(':
            edits.append((it.vis, it.vis, 'pub(crate)'))
        elif it.vis is not None:
            edits.append((it.vis, match_close(toks, it.vis + 1), 'pub(crate)'))
        elif (top or inherent) and it.kind not in ('impl', 'broadcast_use'):
            edits.append((it.kw if not it.mods else next(j for j in range(it.start, it.kw + 1)
                                                         if toks[j].t == it.mods[0]), None, 'pub(crate) '))
        for j in range(it.start, it.kw):
            if toks[j].t == 'closed' and toks[j + 1].t in ('spec', 'fn'):
                edits.append((j, j, 'open'))
        if it.kind == 'fn':
            sg = parse_sig(src, toks, it)
            env = {n: core_type(t)[1] for n, t in sg.params}
            env_by_fn.append((it.start, it.end, env))
        for m in it.members:
            visit(m, False)
    visit(item, True)
    impl_self = None
    if item.kind == 'impl':
        _, trait, self_ty = impl_parts(src, toks, item)
        impl_self = core_type(self_ty)[1]
        if trait and core_type(trait)[1] == 'View':
            j = next(j for j in range(item.kw, item.body[0]) if toks[j].t == 'View')
            edits.append((j, j, 'GoldView'))
            for j in range(item.body[0], item.end):
                if toks[j].t == 'view' and toks[j - 1].t == 'fn':
                    edits.append((j, j, 'gv'))
        else:  # an inherent impl: only its spec methods, renamed (those the crate has too: dropped)
            for m in item.members:
                if m.kind == 'fn' and set(m.mods) & SPEC_MODS:
                    if (impl_self, toks[m.kw + 1].t) in getattr(gold, 'same_methods', ()):
                        edits.append((m.start, m.end, ''))
                    else:
                        edits.append((m.kw + 1, m.kw + 1, 'gold_' + toks[m.kw + 1].t))
            for m in item.members:
                if not (m.kind == 'fn' and set(m.mods) & SPEC_MODS):
                    edits.append((m.start, m.end, ''))
    names = [t.t for t in toks]
    # A gold definition moves to `gold_defs`: the names it took from its own module (that module's
    # items, and what the module imports from the crate) become absolute paths, as `rewrite` does
    # for contract clauses. Names it declares itself (parameters, fields, binders) stay.
    scope = {n: ('crate',) + d.mp + (n,) for n in gold.mod_items.get(d.mp, ()) if n not in gold.copied}
    for doc, a, b in gold.imports.get(d.mp, []):
        for n, _, root, path in flatten_use(doc, a, b, d.mp, gold.mod_items):
            if root == 'crate' and n != '*' and n not in gold.copied:
                scope[n] = tuple(path)
    declared = binders(names[item.start:item.end + 1]) | {
        names[j] for j in range(item.start, item.end) if names[j + 1] == ':'}
    decl_kws = {'fn', 'struct', 'enum', 'union', 'trait', 'type', 'const', 'static', 'mod', 'let'}
    for j in range(item.start, item.end + 1):
        t = names[j]
        if (t in scope and t not in declared and names[j - 1] not in {'.', '::'} | decl_kws
                and (j + 1 > item.end or names[j + 1] not in ('!', ':'))):
            edits.append((j, j, '::'.join(scope[t])))
    for j in range(item.start, item.end + 1):
        env = {}
        for s, e, en in env_by_fn:
            if s <= j <= e:
                env = dict(en)
        if impl_self:
            env['self'] = impl_self
        if toks[j].t == '@' and expr_type(names, expr_before(names, j), j, env, field_types) in gold.views:
            edits.append((j, j, '.gv()'))
        if toks[j].t == '.' and j + 2 <= item.end and toks[j + 2].t == '(' and \
                (expr_type(names, expr_before(names, j), j, env, field_types), toks[j + 1].t) in gold.inherent_spec:
            edits.append((j + 1, j + 1, 'gold_' + toks[j + 1].t))
    out, pos = [], toks[item.start].s
    for a, b, rep in sorted(edits, key=lambda e: (e[0], e[1] is None)):
        if b is None:  # insertion before toks[a]
            if toks[a].s < pos:
                continue
            out.append(src[pos:toks[a].s])
            out.append(rep)
            pos = toks[a].s
            continue
        if toks[a].s < pos:
            continue
        out.append(src[pos:toks[a].s])
        out.append(rep)
        pos = toks[b].e
    out.append(src[pos:toks[item.end].e])
    # doc comments become plain comments: those of removed members would document nothing
    return re.sub(r'^(\s*)//[/!]', r'\1//', ''.join(out), flags=re.M)

# -------------------------------------------------------------------------- generation


def safe_name(key):
    s, tr, f = key
    return '__'.join(x for x in (s.replace('&mut ', 'refmut_').replace('&', 'ref_'), tr, f) if x)


def mentions_capacity(clauses):
    return any(c[k] == '.' and c[k + 1] == 'capacity' for c in clauses for k in range(len(c) - 1))


class Gen:
    """Accumulates the generated module and remembers which lines hold which clause."""

    def __init__(self):
        self.lines, self.where = [], {}

    def add(self, text, tag=None):
        for l in text.split('\n'):
            self.lines.append(l)
            if tag:
                self.where[len(self.lines)] = tag


def join(ts):
    return ' '.join(ts)


def hint_lines(proofs, name, pos):
    """Hint blocks for an obligation: those for every obligation (`*`), then its own (a hint for
    `X` also covers `X__nocap`)."""
    h = proofs['hints']
    own = h.get((name, pos), h.get((name.replace('__nocap', ''), pos), []))
    return h.get(('*', pos), []) + own


def emit_fn(gen, name, generics, recv, self_ty, params, ret, where, requires, ensures, body,
            attrs='', axioms=(), recv_lt=''):
    lt = recv_lt + ' ' if recv_lt else ''
    recv_param = {'&': f'slf: &{lt}{self_ty}', '&mut': f'slf: &{lt}mut {self_ty}', 'self': f'slf: {self_ty}',
                  None: None}[recv]
    ps = ', '.join([p for p in [recv_param] if p] + [f'{n}: {t}' for n, t in params])
    rt = f' -> ({ret[0]}: {ret[1]})' if ret and ret[0] else (f' -> {ret[1]}' if ret else '')
    gen.add(f'{attrs}fn {name}{"<" + generics + ">" if generics else ""}({ps}){rt}', (name, 'sig', None))
    if where:
        gen.add(f'    where {where},', (name, 'sig', None))
    for kw, cl in (('requires', requires), ('ensures', ensures)):
        if cl:
            gen.add(f'    {kw}', (name, 'sig', None))
            for c, orig in cl:
                gen.add(f'        {join(c)},', (name, kw, orig))
    gen.add('{', (name, 'body', None))
    if axioms and not attrs:
        gen.add('    proof {', (name, 'body', None))
        gen.add('        broadcast use ' + ', '.join(axioms) + ';', (name, 'body', None))
        gen.add('    }', (name, 'body', None))
    for l in body:
        gen.add('    ' + l, (name, 'body', None))
    gen.add('}', (name, 'body', None))
    gen.add('')


def maybe_unsized(self_ty, *texts):
    """Whether the type `self_ty` is a type parameter that the generics or where clauses `texts`
    bound by `?Sized` (then `*slf` cannot be moved into a ghost variable)."""
    name = (self_ty or '').strip()
    return bool(IDENT_RE.match(name)) and any(
        re.search(r'(?:^|[<,(\s])' + re.escape(name) + r'\s*:[^,;{]*\?\s*Sized', t or '') for t in texts)


def side_sig(rec, cx):
    """(generics, params, return, where) of a function record, rewritten for the generated module."""
    ty = lambda s: join(rewrite(retok(s), cx)) if s else s
    params = [(n, ty(t)) for n, t in rec.sig.params]
    ret = (rec.sig.ret_name or 'ret', ty(rec.sig.ret_type)) if rec.sig.ret_type else None
    generics = ', '.join(x for x in (rec.gen, rec.sig.generics) if x)
    where = ', '.join(x for x in (getattr(rec, 'impl_where', ''), rec.sig.where) if x)
    return generics, params, ret, ty(where)


def call_expr(rec, cx, args):
    """How the generated module calls the function of a record."""
    if rec.self_ty:
        if rec.trait:
            tcore = core_type(rec.trait)[1]
            tp = cx.verified.trait_path(tcore) or rec.trait
            c = f'<{cx.self_ty} as {tp}>::{rec.sig.name}({args})'
        else:
            c = f'<{cx.self_ty}>::{rec.sig.name}({args})'
    else:
        c = '::'.join(('crate',) + rec.mp + (rec.sig.name,)) + f'({args})'
    return f'unsafe {{ {c} }}' if rec.unsafe else c


def at(cx, mp):
    """The same context, for a clause written in module `mp` (a trait declaration's clauses)."""
    return Ctx(**{**cx.__dict__, 'mp': mp})


def make_ctx(side, rec, src, verified, gold, inv_type):
    gold_names = gold.copied if side == 'gold' else set()
    self_ty = join(rewrite(retok(rec.self_ty), Ctx(side=side, mp=rec.mp, src=src, verified=verified,
                                                   gold_names=gold_names, self_ty=None, self_traits=())))\
        if rec.self_ty else None
    traits = [core_type(rec.trait)[1]] if rec.trait else []
    # supertraits of the impl's trait (and the traits implemented for the type) declare `Self::X`
    for tr, t in verified.traits.items():
        if tr not in traits:
            traits.append(tr)
    return Ctx(side=side, mp=rec.mp, src=src, verified=verified, gold=gold, gold_names=gold_names,
               self_ty=self_ty, self_traits=traits, inv_type=inv_type)


def generate(gold, verified, proofs, invariant, excluded):
    """The generated module (obligations and gold definitions) and one result per gold contract."""
    inv_type = None
    if invariant:
        inv_item = next((d for d in gold.defs if d.kind == 'fn' and d.doc.toks[d.it.kw + 1].t == invariant), None)
        if inv_item is None:
            sys.exit(f'invariant {invariant!r} is not a gold spec function')
        inv_type = core_type(parse_sig(inv_item.doc.text, inv_item.doc.toks, inv_item.it).params[0][1])[1]
    g = Gen()
    g.add('//! GENERATED by compare_specs.py from the gold spec and the verified crate. Do not edit.')
    g.add('#![allow(unused_imports, unused_variables, unused_mut, dead_code, non_snake_case, unused_parens)]')
    g.add('use vstd::prelude::*;\nuse crate::*;')
    contract_mps = sorted({r.mp for rs in verified.fns.values() for r in rs} |
                          {t.mp for t in verified.traits.values()})
    for line in import_block(verified, contract_mps):
        g.add(line)
    for name in sorted(verified.traits):  # every trait's methods, without adding names
        if verified.visible_at_root(verified.traits[name].mp, name):  # (not a trait of a private module)
            g.add(f'use {verified.trait_path(name)} as _;')
    if gold.copied & verified.names:  # some gold names are the crate's too: always `gold_defs::x`
        g.add('use self::gold_defs::{GoldView' + (', GoldInv' if inv_type else '') + '};')
    else:  # no clash: proofs may also name gold definitions directly
        g.add('use self::gold_defs::*;')
    g.add('\nverus! {\n')
    # ---- gold definitions, in their own module
    g.add('// ---- gold spec definitions (closed -> open, `View` -> `GoldView`) ----')
    g.add('pub(crate) mod gold_defs {')
    g.add('use vstd::prelude::*;\nuse crate::*;')
    for line in import_block(gold, sorted({d.mp for d in gold.usable}), local_only=True):
        g.add(line)
    g.add('\npub(crate) trait GoldView {\n    type V;\n    spec fn gv(&self) -> Self::V;\n}\n')
    if inv_type:
        g.add('pub(crate) trait GoldInv {\n    spec fn gold_inv(&self) -> bool;\n}\n')
        g.add(f'// convention: `x@.valid()` on a {inv_type} is read as the gold invariant `{invariant}`')
        g.add(f'impl<T> GoldInv for {inv_type}<T> {{\n    open spec fn gold_inv(&self) -> bool {{\n'
              f'        {invariant}(self)\n    }}\n}}\n')
    cx_defs = Ctx(side='gold', verified=verified)
    for d in gold.usable:
        g.add(rewrite_def_text(d, cx_defs, gold) + '\n')
    for name, text in gold.interpreted.items():
        body = re.sub(r'^(?:pub\S*\s+)?(?:open\s+|closed\s+)?', '', text)
        g.add(f'// @interpret {name} (from the proofs file)\npub(crate) open {body}\n')
    g.add('} // mod gold_defs')
    g.add('\n// ---- proofs (lemmas from the proofs file) ----')
    g.add(proofs['lemmas'])
    g.add('// ---- obligations ----\n')

    results = []
    for key in sorted(gold.fns):
        grecs = gold.fns[key]
        grec = grecs[0]
        greq, gens = gold.contract(grec)
        if not greq and not gens:
            continue
        r = Item(key=key, name=safe_name(key), wrappers=[], note='', h2a=None, errors={}, ext_body=False)
        results.append(r)
        vrecs = verified.fns.get(key, [])
        if len(vrecs) > 1:
            vrecs = [v for v in vrecs if v.mp == grec.mp] or vrecs[:1]
        if not vrecs:
            r.note = 'trusted in the verified crate' if key in verified.trusted else 'no verified counterpart'
            continue
        vrec = vrecs[0]
        r.ext_body = vrec.external_body
        gcx = make_ctx('gold', grec, gold, verified, gold, inv_type)
        vcx = make_ctx('claude', vrec, verified, verified, gold, inv_type)
        gen_txt, gparams, gret, gwhere = side_sig(grec, gcx)
        env = {'slf': core_type(gcx.self_ty)[1] if gcx.self_ty else None,
               **{n: core_type(t)[1] for n, t in gparams}}
        if gret:
            env[gret[0]] = core_type(gret[1])[1]
        used = set()
        for cl in greq + gens:
            ts = rewrite(cl[0], at(gcx, cl[2]), cl[3], env.keys())
            for k, t in enumerate(ts):
                if t == '@':
                    used.add(expr_type(ts, expr_before(ts, k), k, env, verified.field_types))
            used |= {cl[0][k] for k in range(len(cl[0]))} & (gold.uninterp - gold.axiom_covered)
        holes = (used & gold.placeholder_types) | (used & gold.uninterp)
        if holes:
            r.note = 'gold placeholder (uses ' + ', '.join(sorted(holes)) + ')'
            continue
        # Claude => gold
        args = ', '.join((['slf'] if grec.sig.receiver else []) + [n for n, _ in gparams])
        rw = lambda cl, nocap=False: rewrite_contract(cl[0], at(gcx, cl[2]), env, cl[3], nocap)
        needs_nocap = mentions_capacity([c[0] for c in greq + gens]) or any(
            rw(c, True) != rw(c) for c in greq + gens)
        variants = [('', False)] + ([('__nocap', True)] if needs_nocap else [])
        for suffix, nocap in variants:
            name = 'claude_implies_gold__' + r.name + suffix
            if name in excluded:
                r.errors[name] = excluded[name]
                r.wrappers.append((name, nocap))
                continue
            rq = [(rw(c, nocap), c[1]) for c in greq if not (nocap and mentions_capacity([c[0]]))]
            en = []
            for c in gens:
                if nocap and mentions_capacity([c[0]]):
                    continue
                new = rw(c, nocap)
                changed = nocap and new != rw(c)
                en.append((new, c[1] + (' [without capacity]' if changed else '')))
            call = proofs['calls'].get(name) or proofs['calls'].get(name.replace('__nocap', '')) \
                or call_expr(vrec, gcx, args)
            body = []
            if grec.sig.receiver and not maybe_unsized(gcx.self_ty, gen_txt, gwhere):
                body.append('let ghost pre = ' + ('*slf;' if grec.sig.receiver in ('&', '&mut') else 'slf;'))
            body += hint_lines(proofs, name, 'before')
            body.append(f'let ret = {call};' if gret else f'{call};')
            body += hint_lines(proofs, name, 'after')
            if gret:
                body.append('ret')
            emit_fn(g, name, gen_txt, grec.sig.receiver, gcx.self_ty, gparams, gret, gwhere, rq, en, body,
                    axioms=gold.axioms, recv_lt=grec.sig.recv_lt)
            r.wrappers.append((name, nocap))
        # gold => Claude: functions whose verified contract says something
        vreq, vens = verified.contract(vrec)
        if not vreq and not vens:
            continue
        gname = 'gold_contract__' + r.name
        hname = 'gold_implies_claude__' + r.name
        r.h2a = hname
        if hname in excluded or gname in excluded:
            r.errors[hname] = excluded.get(hname) or excluded.get(gname)
            continue
        rq = [(rw(c), c[1]) for c in greq]
        en = [(rw(c), c[1]) for c in gens]
        emit_fn(g, gname, gen_txt, grec.sig.receiver, gcx.self_ty, gparams, gret, gwhere, rq, en,
                ['unimplemented!()'], attrs='#[verifier::external_body]\n', recv_lt=grec.sig.recv_lt)
        agen, aparams, aret, awhere = side_sig(vrec, vcx)
        aenv = {'slf': core_type(vcx.self_ty)[1] if vcx.self_ty else None,
                **{n: core_type(t)[1] for n, t in aparams}}
        if aret:
            aenv[aret[0]] = core_type(aret[1])[1]
        arq = [(rewrite_contract(c[0], at(vcx, c[2]), aenv, c[3]), c[1]) for c in vreq]
        aen = [(rewrite_contract(c[0], at(vcx, c[2]), aenv, c[3]), c[1]) for c in vens]
        aargs = ', '.join((['slf'] if vrec.sig.receiver else []) + [n for n, _ in aparams])
        call = proofs['calls'].get(hname) or f'{gname}({aargs})'
        body = []
        if vrec.sig.receiver and not maybe_unsized(vcx.self_ty, agen, awhere):
            body.append('let ghost pre = ' + ('*slf;' if vrec.sig.receiver in ('&', '&mut') else 'slf;'))
        body += hint_lines(proofs, hname, 'before')
        body.append(f'let ret = {call};' if aret else f'{call};')
        body += hint_lines(proofs, hname, 'after')
        if aret:
            body.append('ret')
        emit_fn(g, hname, agen, vrec.sig.receiver, vcx.self_ty, aparams, aret, awhere, arq, aen, body,
                axioms=gold.axioms, recv_lt=vrec.sig.recv_lt)
    g.add('} // verus!')
    return g, results


def prepare_gold(gold, verified, proofs):
    """Which gold definitions are copied (and how they are referred to), and the interpretations."""
    gold.interpreted = {}
    for name in proofs['interprets']:
        if name not in gold.uninterp:
            sys.exit(f'@interpret {name}: not an uninterpreted function of the gold spec')
        m = re.search(r'^\s*(?:pub\S*\s+)?(?:open\s+|closed\s+)?spec\s+fn\s+' + re.escape(name) + r'\b.*?^\}',
                      proofs['lemmas'], re.M | re.S)
        if not m:
            sys.exit(f'@interpret {name}: the proofs file does not define `spec fn {name}`')
        proofs['lemmas'] = proofs['lemmas'].replace(m.group(0), f'// (spec fn {name}: see gold_defs)')
        gold.uninterp.discard(name)
        gold.interpreted[name] = m.group(0).strip()
    gold.finish()
    # A gold inherent spec method that the verified type defines too, identically (mode, signature
    # and body): gold contracts mean the crate's method, as for same-named types and traits. The
    # other gold inherent spec methods are renamed `gold_..` and copied.
    gold.same_methods = {k for k, v in gold.inherent_bodies.items() if verified.inherent_bodies.get(k) == v}
    gold.inherent_spec -= gold.same_methods
    usable, copied = [], set(gold.interpreted)
    for d in gold.defs:
        toks = d.doc.toks
        if d.kind == 'inherent' and all((core_type(d.self_ty)[1], toks[m.kw + 1].t) in gold.same_methods
                                        for m in d.members):
            continue
        if d.kind in ('struct', 'enum', 'union', 'trait', 'const', 'static', 'type'):
            name = toks[d.it.kw + 1].t
            if name in verified.names:
                continue  # the verified crate has it: gold contracts mean the crate's
        if d.kind == 'fn' and 'uninterp' in d.it.mods and toks[d.it.kw + 1].t in gold.interpreted:
            continue
        if {toks[j].t for j in range(d.it.start, d.it.end + 1)} & verified.trusted_types:
            continue  # about a type the verified crate leaves trusted: cannot be checked
        usable.append(d)
        if d.kind not in ('view', 'inherent', 'broadcast_use'):
            copied.add(toks[d.it.kw + 1 + (d.kind == 'broadcast_group')].t)
    gold.usable, gold.copied = usable, copied

# ------------------------------------------------------------------------------ proofs

FORBIDDEN = re.compile(r'\b(assume|admit|assume_specification|external_body|external_fn_specification|'
                       r'external_type_specification|uninterp|axiom|unsafe)\b|verifier::external|'
                       r'#\[verifier::(?!via_fn)')


def read_proofs(path):
    lemmas, hints, notes, cur, note, interprets, calls = [], {}, {}, None, None, [], {}
    if not os.path.exists(path):
        return {'lemmas': '', 'hints': {}, 'notes': {}, 'interprets': [], 'calls': {}}
    for n, l in enumerate(open(path).read().split('\n'), 1):
        m = re.match(r'\s*//\s*@interpret\s+(\S+)\s*$', l)
        if m:
            interprets.append(m.group(1))
            continue
        m = re.match(r'\s*//\s*@call\s+(\S+)\s+(.+?)\s*$', l)
        if m:
            if FORBIDDEN.search(m.group(2)):
                sys.exit(f'{path}:{n}: proofs may not use trusted constructs: {l.strip()}')
            calls[m.group(1)] = m.group(2)
            continue
        m = re.match(r'\s*//\s*@note\s+(\S+)\s*$', l)
        if m:
            note = m.group(1)
            notes[note] = []
            continue
        if note and re.match(r'\s*//', l):  # the note runs on to the last comment line
            notes[note].append(re.sub(r'^\s*//\s?', '', l).strip())
            continue
        note = None
        m = re.match(r'\s*//\s*@hint\s+(\S+)\s+(before|after)\s*$', l)
        if m:
            cur, depth = (m.group(1), m.group(2)), 0
            hints.setdefault(cur, [])
            continue
        code = l.split('//')[0]
        if FORBIDDEN.search(code):
            sys.exit(f'{path}:{n}: proofs may not use trusted constructs: {l.strip()}')
        if cur:
            if not code.strip():
                continue  # comments and blank lines around the hint block
            hints[cur].append(l)
            depth += code.count('{') - code.count('}')
            if depth == 0:  # the hint's `proof { }` block is complete
                cur = None
        else:
            lemmas.append(l)
    for key, body in hints.items():
        text = '\n'.join(body).strip()
        if text and not (text.startswith('proof {') and text.endswith('}')):
            sys.exit(f'{path}: hint {key[0]} {key[1]} must be a single `proof {{ ... }}` block')
        hints[key] = [l for l in body if l.strip()]
    lemma_text = '\n'.join(lemmas)
    for m in re.finditer(r'^\s*(?:pub\S*\s+)?((?:broadcast )?(?:open |closed )?(?:spec|proof|exec)?\s*fn)\s',
                         lemma_text, re.M):
        if not re.search(r'(spec|proof)\s*fn', m.group(1)):
            sys.exit(f'{path}: only `proof fn` and `spec fn` items are allowed: {m.group(0).strip()}')
    return {'lemmas': lemma_text, 'hints': hints, 'notes': {k: ' '.join(v) for k, v in notes.items()},
            'interprets': interprets, 'calls': calls}

# ------------------------------------------------------------------------------ running


def find_root(path, what, allow_file):
    """The crate at `path`, or the one crate in the folder `path` (or a .rs file, for the gold)."""
    p = os.path.abspath(path)
    if allow_file and os.path.isfile(p) and p.endswith('.rs'):
        return p
    if not os.path.isdir(p):
        sys.exit(f'{what}: no such directory: {path}')
    is_crate = lambda d: os.path.exists(os.path.join(d, 'src', 'lib.rs'))
    if is_crate(p):
        return p
    if os.path.basename(p) == 'src' and is_crate(os.path.dirname(p)):
        return os.path.dirname(p)
    subs = [os.path.join(p, d) for d in sorted(os.listdir(p)) if is_crate(os.path.join(p, d))]
    if len(subs) == 1:
        return subs[0]
    sys.exit(f'{what}: {path} is not a crate (with src/lib.rs) or a folder with exactly one crate'
             + (' (found ' + ', '.join(os.path.basename(s) for s in subs) + ')' if subs else ''))


def run_verus(args, crate, g):
    open(os.path.join(crate, 'src', 'gold_check.rs'), 'w').write('\n'.join(g.lines) + '\n')
    cmd = [os.environ.get('VERUS', 'verus'), '--crate-type=lib']
    for f in args.features:
        cmd += ['--cfg', f'feature="{f}"']
    cmd += list(args.verus_arg) + ['--verify-module', 'gold_check', '--multiple-errors', '1000', 'src/lib.rs']
    r = subprocess.run(cmd, cwd=crate, capture_output=True, text=True)
    return r.stdout + r.stderr


def error_blocks(out):
    return [b for b in re.split(r'\n(?=(?:error|warning|note)(?:\[\w+\])?: )', out)
            if b.startswith('error') and 'aborting due' not in b]


def open_fields(gold, verified, crate):
    """Gold inherent spec methods and views are copied into `gold_defs`, but may read the private
    fields of the verified type they belong to. In the scratch copy of the verified crate, those
    types' private fields become `pub(crate)` (visibility only: no contract changes). Returns the
    names of the types changed."""
    wanted = set()
    for d in gold.usable:
        if d.kind == 'inherent':
            wanted.add(core_type(d.self_ty)[1])
        elif d.kind == 'view':
            wanted.add(core_type(impl_parts(d.doc.text, d.doc.toks, d.it)[2])[1])
    edits, changed = collections.defaultdict(list), []
    for d in verified.defs:
        toks = d.doc.toks
        if d.kind != 'struct' or toks[d.it.kw + 1].t not in wanted or ': ' in d.doc.label:
            continue  # (a struct from a macro invocation cannot be edited)
        if d.it.body:
            lo, hi = d.it.body
        else:  # a tuple struct: `struct S<..>(..);`
            k = d.it.kw + 2
            if toks[k].t == '<':
                k = match_angle(toks, k) + 1
            if toks[k].t != '(':
                continue
            lo, hi = k, match_close(toks, k)
        for f in split_top(toks, lo + 1, hi, angle=True):
            k = 0
            while k < len(f) and f[k].t == '#':
                k = f.index(next(x for x in f[k:] if x.t == ']')) + 1
            if k < len(f) and f[k].t != 'pub':
                edits[d.doc.label].append(f[k].s)
        changed.append(toks[d.it.kw + 1].t)
    for label, offsets in edits.items():
        path = os.path.join(crate, label)
        text = open(path).read()
        for o in sorted(offsets, reverse=True):
            text = text[:o] + 'pub(crate) ' + text[o:]
        open(path, 'w').write(text)
    return sorted(set(changed))


def run(args):
    gold = Source(args.gold, set(args.features))
    verified = Source(args.crate, set(args.features))
    verified.finish()
    proofs = read_proofs(args.proofs)
    prepare_gold(gold, verified, proofs)
    tmp = tempfile.mkdtemp(prefix='compare-specs-')
    crate = os.path.join(tmp, 'crate')
    shutil.copytree(args.crate, crate, ignore=shutil.ignore_patterns('target', '.verus-solver-log', '.verus-log'))
    open(os.path.join(crate, 'src', 'lib.rs'), 'a').write('\n#[cfg(verus_keep_ghost)]\nmod gold_check;\n')
    verified.opened = open_fields(gold, verified, crate)
    excluded = {}
    for _ in range(12):  # drop obligations whose generated code does not compile, then retry
        g, results = generate(gold, verified, proofs, args.invariant, excluded)
        out = run_verus(args, crate, g)
        if re.search(r'verification results:: \d+ verified, \d+ errors', out):
            break
        new = {}
        for b in error_blocks(out):
            locs = re.findall(r'(?:-->|:::) (\S+):(\d+):\d+', b)
            prim = next((int(l) for p, l in locs if p.endswith('gold_check.rs')), None)
            tag = g.where.get(prim) if prim else None
            if tag and tag[0] not in excluded:
                new.setdefault(tag[0], ' '.join(b.split('\n')[0].split()))
        if not new:
            break  # an error outside the obligations: reported as such
        excluded.update(new)
    open(os.path.join(tmp, 'verus_output.txt'), 'w').write(out)
    if args.keep:
        print(f'kept: {crate}/src/gold_check.rs')
    return gold, verified, g, results, out, crate, tmp


def read_line(crate, path, line):
    try:
        return open(os.path.join(crate, path)).read().split('\n')[line - 1].strip()
    except (OSError, IndexError):
        return ''


def classify(g, results, out, crate):
    m = re.search(r'verification results:: (\d+) verified, (\d+) errors', out)
    if not m:
        return None, error_blocks(out)
    failures, foreign = {}, []
    for block in error_blocks(out):
        if not block.startswith('error: '):
            continue
        msg = block.split('\n')[0][7:]
        locs = re.findall(r'(?:-->|:::) (\S+):(\d+):(\d+)', block)
        prim = next(((p, int(l)) for p, l, _ in locs if p.endswith('gold_check.rs')), None)
        tag = g.where.get(prim[1]) if prim else None
        if not tag:
            # an error in a lemma or a gold definition: every result that depends on it is void
            where = f'{prim[0]}:{prim[1]}: {read_line(crate, prim[0], prim[1])}' if prim else 'unknown location'
            foreign.append(f'{msg} ({where})')
            continue
        name, role, clause = tag
        if role in ('requires', 'ensures') and msg.startswith('postcondition'):
            what = f'ensures: {clause}'
        elif msg.startswith('precondition'):
            # the source lines labeled `failed precondition` (a clause may span several lines)
            callee, cur_file, cur_start, cur_line = None, None, None, None
            for bl in block.split('\n'):
                fm = re.search(r'(?:-->|:::) (\S+):(\d+):\d+', bl)
                if fm:
                    cur_file, cur_start = fm.group(1), int(fm.group(2))
                lm = re.match(r'\s*(\d+) \|', bl)
                if lm:
                    cur_line = int(lm.group(1))
                if 'failed precondition' in bl and cur_file and cur_line:
                    callee = (cur_file, cur_line)
                    break
            text = ' '.join(read_line(crate, callee[0], l) for l in range(min(cur_start, callee[1]), callee[1] + 1)) \
                if callee else '?'
            if callee and callee[0].endswith('gold_check.rs') and g.where.get(callee[1]):
                text = g.where[callee[1]][2] or text  # the gold clause as written
            what = 'requires of the callee: ' + text.rstrip(',')
        else:
            what = msg
        failures.setdefault(name, []).append(what)
    if foreign:
        return None, ['Lemmas or gold definitions do not verify, so no obligation result can be '
                      'trusted:'] + foreign
    return failures, None


def fn_label(key):
    s, tr, f = key
    return '::'.join(x for x in (s, tr, f) if x)


def report(args, gold, verified, results, failures, compile_errors, notes, proofs):
    rel = lambda p: os.path.relpath(p, os.path.dirname(os.path.abspath(args.report)))
    lines = ['# Gold spec vs. verified spec', '',
             f'Generated by `compare_specs.py`. Gold spec: `{rel(args.gold)}`; verified crate: '
             f'`{rel(args.crate)}`; proofs: `{rel(args.proofs)}`.', '',
             '- **Claude ⇒ gold**: the verified contract gives everything the gold contract asks for '
             '(gold pre ⇒ Claude pre, and gold pre ∧ Claude post ⇒ gold post).',
             '- **gold ⇒ Claude**: the gold contract gives everything the verified contract promises '
             '(gold pre ∧ gold post ⇒ Claude\'s; a trait method\'s contract includes the trait '
             'declaration\'s, for traits the crate defines).',
             '- Conventions: gold definitions are copied into `gold_defs` (`closed` -> `open`; `View` -> '
             '`GoldView`)'
             + (f'; gold spec methods of inherent impls that the verified crate defines identically are the '
                f'crate\'s: ' + ', '.join(f'`{t}::{m}`' for t, m in sorted(gold.same_methods))
                if getattr(gold, 'same_methods', None) else '')
             + (f'; gold spec methods of inherent impls are renamed: '
                + ', '.join(f'`{t}::{m}` -> `gold_{m}`' for t, m in sorted(gold.inherent_spec)) if gold.inherent_spec else '')
             + (f'; `x@.valid()` is read as `{args.invariant}`' if args.invariant else '')
             + '; gold axioms in force: ' + (', '.join(f'`{a}`' for a in gold.axioms) or 'none')
             + ('; private fields read by copied gold definitions are `pub(crate)` in the scratch copy of the '
                'verified crate: ' + ', '.join(f'`{t}`' for t in verified.opened) if getattr(verified, 'opened', None) else '')
             + (f'; external specifications (of items outside the crate) are neither compared nor copied: '
                f'{len(gold.external_specs)} in the gold spec, {len(verified.external_specs)} in the verified crate'
                if gold.external_specs or verified.external_specs else '')
             + f'; cfg: features {sorted(args.features) or "none"}, pointer width {PTR_WIDTH}.',
             '- *capacity only*: the obligation fails, but holds once capacity clauses are removed.',
             '- *does not compile*: the generated obligation does not compile (for example, the two '
             'signatures differ), so the contracts were not compared; the compiler\'s message is shown.']
    if gold.interpreted:
        lines += ['', 'Gold placeholders read in terms of the verified crate (`@interpret`, a modeling '
                  'choice, not checked):', '']
        for name, text in gold.interpreted.items():
            lines += ['```rust', text, '```']
    if proofs['calls']:
        lines += ['', 'Calls adapted to the verified signature (`@call`, a modeling choice):', '']
        lines += [f'- `{k}`: `{v}`' for k, v in sorted(proofs['calls'].items())]
    if gold.warnings or verified.warnings:
        lines += ['', 'Warnings while reading the specs:', ''] + [f'- {w}' for w in gold.warnings + verified.warnings]
    lines.append('')
    if compile_errors is not None:
        lines += ['**The gold definitions or the proofs do not compile or verify:**', '', '```'] + \
            [e[:1500] for e in compile_errors[:10]] + ['```']
        open(args.report, 'w').write('\n'.join(lines) + '\n')
        return 2

    def status(r, name):
        if name in r.errors:
            return 'does not compile'
        return 'proved' if name not in failures else 'UNPROVED'
    rows, details, bad, noted, capacity_only = [], [], 0, set(), set()
    nfail = 0
    for r in results:
        label = fn_label(r.key)
        note = r.note + (' contract trusted (`external_body`) in the verified crate' if r.ext_body else '')
        if not r.wrappers and not r.h2a:
            rows.append(f'| `{label}` | — | — | {note.strip()} |')
            continue
        full = next((n for n, nc in r.wrappers if not nc), None)
        nocap = next((n for n, nc in r.wrappers if nc), None)
        s = status(r, full) if full else '—'
        if s == 'UNPROVED' and nocap and status(r, nocap) == 'proved':
            s = 'capacity only'
        h = status(r, r.h2a) if r.h2a else '—'
        if s in ('UNPROVED', 'does not compile') and not notes.get(full):
            bad += 1
        rows.append(f'| `{label}` | {s} | {h} | {note.strip()} |')
        for n in [x for x, _ in r.wrappers] + ([r.h2a] if r.h2a else []):
            if n in failures or n in r.errors:
                nfail += 1
                items = [f'- does not compile: {r.errors[n]}'] if n in r.errors else [f'- {w}' for w in failures[n]]
                details += ['', f'### `{n}`', ''] + items
                nt = notes.get(n, notes.get(n.replace('__nocap', '')))
                if n == full and s == 'capacity only':
                    capacity_only.add(n)
                    details += ['', '*Capacity only:* the capacity-free variant is proved.']
                elif nt:
                    noted.add(n)
                    details += ['', f'*Note (an explanation, not checked):* {nt}']

    def summary(col, label):
        counts = {}
        for row in rows:
            c = row.split('|')[col].strip()
            counts[c] = counts.get(c, 0) + 1
        return f'{label}: ' + ', '.join(f'{v} {k}' for k, v in sorted(counts.items()) if k != '—') \
            + f', {counts.get("—", 0)} not compared.'
    lines += ['| function | Claude ⇒ gold | gold ⇒ Claude | note |', '|---|---|---|---|'] + rows
    lines += ['', summary(2, 'Claude ⇒ gold'), '', summary(3, 'gold ⇒ Claude')]
    wrappers = {n for r in results for n, _ in r.wrappers} | {r.h2a for r in results if r.h2a}
    errs = {n for r in results for n in r.errors}
    stale = sorted(k for k in notes if k not in failures and k + '__nocap' not in failures and k not in errs)
    if stale:
        lines += ['', 'Notes for obligations that are proved or do not exist: '
                  + ', '.join(f'`{k}`' + ('' if k in wrappers else ' (does not exist)') for k in stale) + '.']
    if details:
        lines += ['', f'## Obligations not proved ({nfail}: {len(capacity_only)} capacity only, '
                  f'{len(noted)} with a note, {nfail - len(capacity_only) - len(noted)} unexplained)'] + details
    open(args.report, 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(l for l in lines if l.startswith(('Claude ⇒ gold:', 'gold ⇒ Claude:', 'Notes for', '## Obligations'))))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description='Compare the gold spec with the verified spec.')
    ap.add_argument('verus_fixed', help='the verified crate (its root, or a folder that contains it)')
    ap.add_argument('human_spec', help='the gold spec: a crate source tree (or a folder with one), or a .rs file')
    ap.add_argument('--proofs', default=os.path.join(HERE, 'spec_proofs.rs'))
    ap.add_argument('--report', default=os.path.join(HERE, 'spec_comparison.md'))
    ap.add_argument('--features', nargs='*', default=[], help='cargo features that are enabled')
    ap.add_argument('--invariant', default='',
                    help='gold spec function that `x@.valid()` on its argument type is read as')
    ap.add_argument('--verus-arg', action='append', default=[], help='extra argument for verus (repeatable)')
    ap.add_argument('--keep', action='store_true', help='keep the scratch crate')
    args = ap.parse_args()
    args.crate = find_root(args.verus_fixed, 'VERUS_FIXED', False)
    args.gold = find_root(args.human_spec, 'HUMAN_SPEC', True)
    gold, verified, g, results, out, crate, tmp = run(args)
    failures, compile_errors = classify(g, results, out, crate)
    proofs = read_proofs(args.proofs)
    code = report(args, gold, verified, results, failures, compile_errors, proofs['notes'], proofs)
    if compile_errors is not None:
        print('the gold definitions or the proofs do not compile or verify; see', args.report)
    if not args.keep:
        shutil.rmtree(tmp, ignore_errors=True)
    print('report:', args.report)
    sys.exit(code)


if __name__ == '__main__':
    main()