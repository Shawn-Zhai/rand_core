#!/usr/bin/env python3
"""Classic line-by-line diff of the specifications in two versions of a Verus crate.

ORIGINAL is a crate with Verus specifications and proofs; AMENDED is an amended copy of it. The
*specification* is:

  - the `requires` and `ensures` clauses of every function that is not a proof function (executable
    functions, trait method declarations, `assume_specification`), and
  - the spec functions that these clauses use, directly or through other spec functions (by name;
    `x@` uses `view`), in either crate.

Comments, signatures, lemmas (proof functions), proof code and executable code are not part of it
(`--lemmas` adds the `requires`/`ensures` of proof functions, and the spec functions those use;
`--comments` keeps comment lines inside the specification).

Both crates are split into items (functions, spec and proof functions, traits, impls, ...), matched
by name (module, impl or trait, item) rather than by position. The specification lines of each pair
are compared with a classic line-by-line diff (`difflib`, as `diff -u`); hunk headers give the real
line numbers in the source files, and the function's signature, as `diff -p` does. The report shows
each changed item with links to its lines in both crates; the same hunks are also written as one
unified diff (--diff). Changes outside the specification (lemmas, proofs, imports, documentation,
executable code) are not diffed, but are counted and listed, so that the report covers every change.

A *clause* is one comma-separated expression after `requires` or `ensures`. Each item's report
lists the clauses that the amendment adds or removes (compared token by token, up to the name of
the result and trailing commas), with the kind the notes give them.

Notes (--notes, default `amendment_notes.json` next to this script) explain what a changed item
brought, by its `key`: `value`, a list of kinds from VALUE_KINDS; `clauses`, the kind of each added
clause ({fragment of the clause's text: kind}, `*` for the rest; an item with one kind gives it to
all its clauses); and `agent_note`, an explanation. The file is a list of notes, or
{"summary": Markdown, "items": [notes]}. --template adds an empty note for each changed item that
has none.

Usage:
    python3 spec_diff.py ORIGINAL AMENDED [--notes FILE] [--report FILE] [--diff FILE]
                         [--template] [--lemmas] [--comments] [-w] [--context N]
ORIGINAL and AMENDED are crates (their root or their `src/`). For rand_core, from the repository
root:
    python3 spec_amendment_diff/spec_diff.py verus verus_fixed
"""
import argparse
import collections
import difflib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# What a change brought, relative to the specification the amendment was checked against (the
# reference, such as a developer's).
VALUE_KINDS = {
    'gap': 'adds a true guarantee that the original contract lacked: callers can prove more',
    'precondition': 'weakens a precondition that rejected valid calls',
    'restatement': "states a reference clause that already follows from the original's contract: "
                   'nothing new for callers, but the two specs are now visibly reconciled',
    'bridge': "ghost definitions or lemmas that relate the reference's vocabulary to the original's",
    'proof': "proof work needed to prove the reference's clauses",
    'trust': "a change of the trusted base needed to use the reference's vocabulary",
    'reference-defect': 'deviates from the reference where the reference is wrong',
    'doc': 'comments and documentation only',
}

# what a changed line is counted as, in the report
STATS = ('spec', 'comment', 'lemma', 'proof', 'exec', 'other')
SPEC_KW = ('requires', 'ensures')

# ------------------------------------------------------------------------------------ tokens

Tok = collections.namedtuple('Tok', 'kind text line end_line start stop')

PUNCT = ['<==>', '==>', '<==', '===', '!==', '&&&', '|||', '..=', '...', '<<=', '>>=', '::', '->',
         '=>', '==', '!=', '<=', '>=', '&&', '||', '<<', '>>', '+=', '-=', '*=', '/=', '%=', '^=',
         '&=', '|=', '..']
PUNCT_RE = re.compile('|'.join(re.escape(p) for p in PUNCT) + r'|[^\sA-Za-z0-9_]')
RAW_RE = re.compile(r'b?r(#*)"')
CHAR_RE = re.compile(r"b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]*\}|.)|[^\\'\n])'")
LIFETIME_RE = re.compile(r"'[A-Za-z_][A-Za-z0-9_]*")
NUM_RE = re.compile(r'\d[0-9A-Za-z_]*(?:\.(?![.A-Za-z_])[0-9][0-9A-Za-z_]*)?')
IDENT_RE = re.compile(r'(?:r#)?[A-Za-z_][A-Za-z0-9_]*')


def tokenize(text):
    """Rust tokens (with Verus's operators), comments included, with their first and last line."""
    toks, i, n, line = [], 0, len(text), 1
    while i < n:
        c = text[i]
        if c.isspace():
            line += c == '\n'
            i += 1
            continue
        kind = 'code'
        if text.startswith('//', i):
            j = text.find('\n', i)
            j, kind = (n if j < 0 else j), 'comment'
        elif text.startswith('/*', i):
            depth, j, kind = 1, i + 2, 'comment'
            while j < n and depth:
                if text.startswith('/*', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('*/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
        elif RAW_RE.match(text, i):
            m = RAW_RE.match(text, i)
            j = text.find('"' + m.group(1), m.end())
            j = n if j < 0 else j + 1 + len(m.group(1))
        elif c == '"' or text.startswith('b"', i):
            j = i + 1 + (c == 'b')
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j += 1
        else:
            m = (CHAR_RE.match(text, i) or LIFETIME_RE.match(text, i) or NUM_RE.match(text, i)
                 or IDENT_RE.match(text, i) or PUNCT_RE.match(text, i))
            j = m.end()
        s = text[i:j]
        toks.append(Tok(kind, s, line, line + s.count('\n'), i, j))
        line += s.count('\n')
        i = j
    return toks


# ------------------------------------------------------------------------------------- items

CONTRACT_KW = {'requires', 'ensures', 'recommends', 'decreases', 'opens_invariants', 'no_unwind',
               'returns', 'default_ensures', 'when', 'via'}
# specification clauses that can appear inside executable code (loops, closures)
BODY_SPEC_KW = {'requires', 'ensures', 'recommends', 'decreases', 'invariant',
                'invariant_except_break', 'opens_invariants', 'no_unwind'}
# after one of these, a `{` starts an expression, not a function or loop body
EXPR_BEFORE = {'<==>', '==>', '<==', '&&', '||', '&&&', '|||', '==', '!=', '===', '!==', '=', '=>',
               '+', '-', '*', '/', '%', '!', '<', '>', '<=', '>=', '|', '&', '^', 'else', 'in',
               'return', '..', '..='}
BINDER_AFTER = {'forall', 'exists', 'choose', None, '(', ',', '=', '=>', '==>', '<==>', '&&', '&&&',
                '|||', 'return'}
MODIFIERS = {'open', 'closed', 'uninterp', 'default', 'unsafe', 'async', 'tracked', 'ghost',
             'axiom', 'broadcast'}
EXTERNAL_SPEC_RE = re.compile(r'external_(?:fn|type|trait)_specification|external_trait_extension')
EXTERNAL_RE = re.compile(r'verifier::external\b(?!_)')
OPEN, CLOSE = '([{', ')]}'


class Item:
    def __init__(self, key, kind, module, file):
        self.key, self.kind, self.module, self.file = key, kind, module, file
        self.mode = self.name = self.ret = self.sig_line = None
        self.trusted = set()
        # line number -> category: 'contract' (requires/ensures of a function that is not a proof
        # function), 'lemma' (requires/ensures of a proof function), 'specfn' (a spec function),
        # 'sig' (the rest of a function's header), 'decl', 'doc', 'proof' or 'exec'
        self.lines = {}
        self.comments = set()  # comment-only lines
        self.clauses = []      # requires/ensures: [(keyword, text, normalized tokens, first line, last line)]
        self.tokens = collections.defaultdict(list)   # category -> code tokens
        self.involved = False  # a spec function that the specification uses

    @property
    def short(self):
        return self.key.split(' :: ', 1)[1] if ' :: ' in self.key else self.key

    @property
    def span(self):
        return (min(self.lines), max(self.lines)) if self.lines else (0, 0)


class SourceFile:
    """One `.rs` file, split into items; every line gets an item and a category."""

    def __init__(self, crate, path, module):
        self.crate, self.path, self.module = crate, path, module
        text = open(os.path.join(crate.src, path), encoding='utf-8').read()
        self.text_lines = text.split('\n')
        self.all = tokenize(text)
        self.code = [t for t in self.all if t.kind == 'code']
        self.source = text
        self.C = [t.text for t in self.code] + ['<eof>'] * 4
        n = len(self.code)
        self.cat, self.owner = [None] * n, [None] * n
        self.pair = [None] * n
        stack = []
        for i, t in enumerate(self.C[:n]):
            if t in OPEN:
                stack.append(i)
            elif t in CLOSE and stack and OPEN[CLOSE.index(t)] == self.C[stack[-1]]:
                j = stack.pop()
                self.pair[i], self.pair[j] = j, i
        self.special = {}      # (module, kind) -> Item for `module` and `imports`
        self.items(0, n, 'rust', module, f'{module} :: ')
        self.assign_lines()

    # -- helpers over code tokens

    def close(self, j):
        """Index of the bracket matching the one at j (or j itself if unmatched)."""
        return self.pair[j] if self.pair[j] is not None else j

    def until(self, j, hi, stops):
        """First index >= j whose token is in `stops`, jumping over bracketed groups."""
        while j < hi:
            t = self.C[j]
            if t in stops:
                return j
            j = self.close(j) + 1 if t in OPEN else j + 1
        return hi - 1

    def skip_angles(self, j):
        depth = 0
        while j < len(self.code):
            t = self.C[j]
            depth += {'<': 1, '<<': 2, '>': -1, '>>': -2}.get(t, 0)
            j = self.close(j) + 1 if t in OPEN else j + 1
            if depth <= 0:
                return j
        return j

    def body_brace(self, j, hi):
        """Index of the `{` or `;` that ends a specification region starting at j: a `{` that does not
        start an expression (a block after an operator, the arms of `match`, `if`, ...)."""
        pending, prev = 0, None
        while j < hi:
            t = self.C[j]
            if t == ';':
                return j
            if t in CLOSE:
                return j
            if t == '{':
                if pending or prev in EXPR_BEFORE:
                    pending = max(pending - 1, 0)
                    j, prev = self.close(j) + 1, '}'
                    continue
                return j
            if t in ('(', '['):
                j, prev = self.close(j) + 1, ')'
                continue
            if t in ('match', 'if', 'while', 'for', 'unsafe', 'loop') and prev != '.':
                pending += 1
            prev = t
            j += 1
        return hi - 1

    def mark(self, lo, hi, item, cat):
        """Tokens lo..hi (inclusive) belong to `item`, in category `cat` (unless already marked)."""
        for k in range(lo, min(hi, len(self.code) - 1) + 1):
            if self.owner[k] is None:
                self.owner[k], self.cat[k] = item, cat

    def new_item(self, key, kind, module):
        key0, n = key, 2
        while key in self.crate.items:
            key, n = f'{key0} #{n}', n + 1
        item = Item(key, kind, module, self.path)
        self.crate.items[key] = item
        return item

    def special_item(self, module, kind):
        if (module, kind) not in self.special:
            self.special[(module, kind)] = self.new_item(f'{module} :: {kind}', kind, module)
        return self.special[(module, kind)]

    # -- items

    def items(self, lo, hi, ctx, module, prefix, trusted=()):
        """Parse the items in code[lo:hi]. ctx: 'verus' inside `verus!`, 'rust' outside."""
        C, i = self.C, lo
        while i < hi:
            start, attrs = i, []
            while C[i] == '#' and C[i + 1] in ('[', '!'):
                if C[i + 1] == '!':                    # inner attribute
                    end = self.close(i + 2)
                    self.mark(i, end, self.special_item(module, 'module'), 'decl')
                    i = start = end + 1
                    continue
                end = self.close(i + 1)
                attrs.append(' '.join(C[i:end + 1]))
                i = end + 1
            if i >= hi:
                self.mark(start, hi - 1, self.special_item(module, 'module'), 'decl')
                break
            mods = []
            while True:
                t = C[i]
                if t == 'pub':
                    i = self.close(i + 1) + 1 if C[i + 1] == '(' else i + 1
                elif t in MODIFIERS or (t == 'const' and C[i + 1] in ('fn', 'unsafe', 'async')):
                    mods.append(t)
                    i += 1
                elif t in ('spec', 'proof', 'exec') and C[i + 1] in ('fn', '('):
                    mods.append(t)
                    i = self.close(i + 1) + 1 if C[i + 1] == '(' else i + 1
                elif t == 'extern' and self.code[i + 1].text.startswith('"'):
                    i += 2
                else:
                    break
            attr_text = ' '.join(attrs)
            external = bool(EXTERNAL_RE.search(attr_text))
            sub = 'rust' if external else ctx
            reasons = set(trusted)
            if 'external_body' in attr_text:
                reasons.add('external_body')
            if EXTERNAL_SPEC_RE.search(attr_text):
                reasons.add('external specification')
            t = C[i]
            if t == 'fn':
                i = self.fn(start, i, hi, sub, mods, module, prefix, reasons)
            elif t == 'use':
                end = self.until(i, hi, {';'})
                if 'broadcast' in mods and ctx == 'verus':
                    self.mark(start, end, self.special_item(module, 'broadcast use'), 'decl')
                else:
                    self.mark(start, end, self.special_item(module, 'imports'), 'decl')
                i = end + 1
            elif t == 'group' and 'broadcast' in mods:
                end = self.until(i, hi, {'{', ';'})
                end = self.close(end) if C[end] == '{' else end
                item = self.new_item(f'{prefix}broadcast group {C[i + 1]}', 'broadcast group', module)
                self.mark(start, end, item, 'decl')
                i = end + 1
            elif t in ('struct', 'enum', 'union', 'type', 'const', 'static', 'global'):
                end = self.until(i, hi, {';', '{'})
                if C[end] == '{':
                    end = self.close(end)
                    end += C[end + 1] == ';'
                name = C[i + 1] if t != 'global' else ' '.join(C[i + 1:end])
                kind = {'global': 'global'}.get(t, t)
                item = self.new_item(f'{prefix}{t} {name}', kind, module)
                item.trusted |= reasons | ({'global'} if t == 'global' else set())
                cat = 'specfn' if 'spec' in mods else 'decl' if sub == 'verus' else 'exec'
                self.mark(start, end, item, cat)
                i = end + 1
            elif t in ('trait', 'impl'):
                brace = self.until(i, hi, {'{', ';'})
                key = f'trait {C[i + 1]}' if t == 'trait' else self.impl_name(i, brace)
                item = self.new_item(prefix + key, t, module)
                item.trusted |= reasons
                cat = 'decl' if sub == 'verus' else 'exec'
                self.mark(start, brace, item, cat)
                if C[brace] == '{':
                    end = self.close(brace)
                    self.mark(end, end, item, cat)
                    self.items(brace + 1, end, sub, module, f'{prefix}{key} :: ',
                               reasons if 'external specification' in reasons else ())
                    i = end + 1
                else:
                    i = brace + 1
            elif t == 'mod':
                name = C[i + 1]
                item = self.new_item(f'{prefix}mod {name}', 'mod', module)
                if C[i + 2] == '{':
                    end = self.close(i + 2)
                    self.mark(start, i + 2, item, 'decl')
                    self.mark(end, end, item, 'decl')
                    inner = f'{module}::{name}'
                    self.items(i + 3, end, sub, inner, f'{inner} :: ')
                    i = end + 1
                else:
                    self.mark(start, i + 2, item, 'decl')
                    i = i + 3
            elif t == 'extern' and C[i + 1] == 'crate':
                end = self.until(i, hi, {';'})
                self.mark(start, end, self.special_item(module, 'imports'), 'decl')
                i = end + 1
            elif t == 'assume_specification':
                end = self.until(i, hi, {';'})
                target = ''.join(C[i + 1:self.close(i + 1) + 1]) if C[i + 1] == '<' else ''
                k = self.skip_angles(i + 1) if C[i + 1] == '<' else i + 1
                target = ' '.join(C[k + 1:self.close(k)]) if C[k] == '[' else target
                item = self.new_item(f'{prefix}assume_specification [{target}]',
                                     'assume_specification', module)
                item.trusted.add('assume_specification')
                item.mode, item.sig_line = 'exec', self.code[i].line
                self.contract(item, k, end, 'contract')
                self.mark(start, end, item, 'sig')
                i = end + 1
            elif re.fullmatch(r'[A-Za-z_]\w*', t) and (C[i + 1] == '!' or C[i + 1] == '::'):
                k = i
                while C[k + 1] == '::':
                    k += 2
                if C[k + 1] != '!' or C[k + 2] not in OPEN and C[k + 2] != 'macro_rules':
                    self.mark(i, i, self.special_item(module, 'module'), 'decl' if ctx == 'verus' else 'exec')
                    i += 1
                    continue
                name = C[k]
                g = k + 2 if C[k + 2] in OPEN else k + 3   # `macro_rules! name {`
                end = self.close(g)
                end += C[end + 1] == ';'
                if name == 'verus' and C[g] == '{':
                    mod_item = self.special_item(module, 'module')
                    self.mark(start, g, mod_item, 'decl')
                    self.mark(end, end, mod_item, 'decl')
                    self.items(g + 1, self.close(g), 'verus', module, prefix)
                else:
                    label = f'macro {C[k + 2]}' if name == 'macro_rules' else f'{name}!'
                    item = self.new_item(prefix + label, 'macro', module)
                    self.mark(start, end, item, 'exec')
                i = end + 1
            else:
                self.mark(start, i, self.special_item(module, 'module'), 'decl' if ctx == 'verus' else 'exec')
                i += 1

    def impl_name(self, i, brace):
        """`impl Trait for Type`, without generics or where clause."""
        C, k, out = self.C, i + 1, ['impl']
        if C[k] == '<':
            k = self.skip_angles(k)
        depth = 0
        while k < brace and C[k] != 'where':
            t = C[k]
            if t in ('<', '<<', '>', '>>'):
                depth += {'<': 1, '<<': 2, '>': -1, '>>': -2}[t]
            elif depth == 0:
                out.append(t)
            k += 1
        s = ' '.join(out)
        s = re.sub(r'\s*::\s*', '::', s)
        return re.sub(r'& (mut )?', lambda m: '&' + (m.group(1) or ''), s)

    def fn(self, start, k, hi, ctx, mods, module, prefix, reasons):
        C = self.C
        name, j = C[k + 1], k + 2
        if C[j] == '<':
            j = self.skip_angles(j)
        if C[j] != '(':
            self.mark(start, j, self.special_item(module, 'module'), 'exec')
            return j + 1
        j = self.close(j) + 1
        ret = None
        if C[j] == '->' and C[j + 1] == '(':
            n = j + 3 if C[j + 2] in ('tracked', 'ghost') else j + 2
            if C[n + 1] == ':' and C[n + 2] != ':':
                ret = C[n]
        while j < hi and C[j] not in CONTRACT_KW | {'{', ';'}:
            j = self.close(j) + 1 if C[j] in ('(', '[') else j + 1
        contract = j if C[j] in CONTRACT_KW else None
        body = self.body_brace(j, hi) if contract is not None else j
        mode = 'spec' if 'spec' in mods else 'proof' if {'proof', 'axiom'} & set(mods) else 'exec'
        kind = ('broadcast ' if 'broadcast' in mods else '') + ('axiom' if 'axiom' in mods else mode) + ' fn'
        item = self.new_item(f'{prefix}fn {name}', kind, module)
        item.mode, item.name, item.ret, item.sig_line = mode, name, ret, self.code[k].line
        item.trusted |= reasons | ({'axiom'} if 'axiom' in mods else set())
        end = self.close(body) if C[body] == '{' else body
        if ctx == 'rust':
            self.mark(start, end, item, 'exec')
            return end + 1
        if mode == 'spec':
            self.mark(start, end, item, 'specfn')
            return end + 1
        if contract is not None:
            self.contract(item, contract, body, 'lemma' if mode == 'proof' else 'contract')
        self.mark(start, body, item, 'sig')
        if C[body] == '{':
            self.mark(end, end, item, 'sig')
            if mode == 'proof':
                self.mark(body + 1, end - 1, item, 'proof')
            else:
                self.exec_body(body + 1, end, item)
            for x in range(body + 1, end):
                if C[x] in ('assume', 'admit') and C[x + 1] == '(' and self.cat[x] == 'proof':
                    item.trusted.add(C[x])
        return end + 1

    def exec_body(self, lo, hi, item):
        """Mark the ghost code in an executable body code[lo:hi] as proof, the rest as exec."""
        C, j = self.C, lo
        while j < hi:
            t, prev = C[j], C[j - 1]
            end = None
            if t == 'proof' and C[j + 1] == '{':
                end = self.close(j + 1)
            elif t in ('assert', 'assume') and C[j + 1] in ('(', 'forall', 'exists') and prev != '.':
                end = self.ghost_stmt_end(j, hi)
            elif t == 'let' and C[j + 1] in ('ghost', 'tracked'):
                end = self.until(j, hi, {';'})
            elif t in BODY_SPEC_KW and prev != '.' and C[j + 1] != '(':
                end = self.body_brace(j + 1, hi) - 1
            if end is not None:
                self.mark(j, end, item, 'proof')
                j = end + 1
            else:
                self.mark(j, j, item, 'exec')
                j += 1

    def ghost_stmt_end(self, j, hi):
        C, k = self.C, j + 1
        while k < hi:
            t = C[k]
            if t == ';':
                return k
            if t in CLOSE:
                return k - 1
            if t == 'by':
                k += 1
                if C[k] == '(':
                    k = self.close(k) + 1
                if C[k] in ('requires', 'ensures'):
                    k = self.body_brace(k + 1, hi)
                if C[k] == '{':
                    k = self.close(k)
                    return k + (C[k + 1] == ';')
                return k if C[k] == ';' else k - 1
            k = self.close(k) + 1 if t in OPEN else k + 1
        return hi - 1

    def contract(self, item, lo, hi, cat):
        """Split the contract code[lo:hi] into clauses; mark the requires and ensures (the keyword and
        its clauses) as `cat`."""
        C, j, kw, start, prev, region = self.C, lo, None, None, None, None

        def flush(end):
            if kw in SPEC_KW and start is not None and end > start:
                toks = self.code[start:end]
                norm = tuple('$ret' if t.text == item.ret else t.text for k, t in enumerate(toks, start)
                             if not (t.text == ',' and self.C[k + 1] in CLOSE))
                item.clauses.append((kw, self.render(start, end), norm, toks[0].line, toks[-1].end_line))

        def close_region(end):
            if kw in SPEC_KW and region is not None:
                self.mark(region, end - 1, item, cat)

        while j < hi:
            t = C[j]
            if t in CONTRACT_KW and prev != '.':
                flush(j)
                close_region(j)
                kw, start, prev, region = t, j + 1, None, j
                j += 1
                continue
            if t == ',':
                flush(j)
                start, prev = j + 1, None
                j += 1
                continue
            if t == '|' and prev in BINDER_AFTER:
                k = j + 1
                while k < hi and C[k] != '|':
                    k = self.close(k) + 1 if C[k] in OPEN else k + 1
                j, prev = k + 1, '|'
                continue
            j, prev = (self.close(j) + 1, ')') if t in OPEN else (j + 1, t)
        flush(hi)
        close_region(hi)

    def render(self, lo, hi):
        """The source text of code[lo:hi] on one line: comments dropped, line breaks and indentation
        collapsed to one space (none inside brackets)."""
        out, prev = [], None
        for k, t in enumerate(self.code[lo:hi], lo):
            if t.text == ',' and self.C[k + 1] in CLOSE:
                continue
            if prev is not None and self.source[prev.stop:t.start]:
                if not (prev.text in ('(', '[') or t.text in (')', ']', ',')):
                    out.append(' ')
            out.append(t.text)
            prev = t
        return ''.join(out)

    # -- lines

    def assign_lines(self):
        """Comments go with the next code token (the previous one before a closing bracket); a line
        takes the item and category of its first token; a blank line inside an item, of the next
        line."""
        code_idx, k = [], -1
        for t in self.all:
            if t.kind == 'code':
                k += 1
            code_idx.append(k)
        n = len(self.code)
        line_of = {}
        for idx, t in enumerate(self.all):
            if t.kind == 'code':
                k = code_idx[idx]
                own, cat = self.owner[k], self.cat[k]
            else:
                nxt = code_idx[idx] + 1
                inner_doc = t.text.startswith(('//!', '/*!'))
                ref = nxt if nxt < n and self.C[nxt] not in CLOSE else nxt - 1
                if ref < 0:
                    ref = 0 if n else None
                own = self.owner[ref] if ref is not None else None
                cat = self.cat[ref] if ref is not None else 'doc'
                if inner_doc or own is None:
                    own = self.special_item(own.module if own else self.module, 'module')
                    cat = 'doc'
            if own is None:
                own, cat = self.special_item(self.module, 'module'), 'doc'
            for ln in range(t.line, t.end_line + 1):
                if ln not in line_of and t.kind == 'comment':
                    own.comments.add(ln)
                line_of.setdefault(ln, (own, cat))
        filled = {}
        nxt = None
        for ln in range(len(self.text_lines), 0, -1):
            if ln in line_of:
                nxt = line_of[ln]
                filled[ln] = nxt
            else:
                prev = next((line_of[p] for p in range(ln - 1, 0, -1) if p in line_of), None)
                if nxt and prev and prev[0] is nxt[0]:
                    filled[ln] = nxt
        for ln, (own, cat) in filled.items():
            own.lines[ln] = cat
        for k, t in enumerate(self.code):
            if self.owner[k] is not None:
                self.owner[k].tokens[self.cat[k]].append(t.text)


class Crate:
    def __init__(self, path, what):
        root = os.path.abspath(path)
        if not os.path.isdir(root):
            sys.exit(f'{what}: no such directory: {path}')
        if os.path.basename(root) == 'src' and os.path.exists(os.path.join(os.path.dirname(root), 'Cargo.toml')):
            root = os.path.dirname(root)
        self.root = root
        self.src = os.path.join(root, 'src')
        if not os.path.isdir(self.src):
            sys.exit(f'{what}: {path} has no src/')
        self.items, self.files = {}, {}
        for dirpath, _, names in sorted(os.walk(self.src)):
            for name in sorted(names):
                if name.endswith('.rs'):
                    rel = os.path.relpath(os.path.join(dirpath, name), self.src)
                    self.files[rel] = SourceFile(self, rel, module_of(rel))
        self.by_short = collections.defaultdict(list)
        for item in self.items.values():
            self.by_short[item.short].append(item)

    def mark_involved(self, lemmas):
        """Mark the spec functions that the specification uses, directly or through other spec
        functions (by name; `x@` is `x.view()`)."""
        def names(tokens):
            out = {t for t in tokens if re.fullmatch(r'[A-Za-z_]\w*', t)}
            return out | ({'view'} if '@' in tokens else set())
        used = set()
        for item in self.items.values():
            used |= names(item.tokens['contract'] + (item.tokens['lemma'] if lemmas else []))
        spec_fns = [i for i in self.items.values() if i.mode == 'spec']
        changed = True
        while changed:
            changed = False
            for item in spec_fns:
                if not item.involved and item.name in used:
                    item.involved = changed = True
                    used |= names(item.tokens['specfn'])

    def line(self, item, ln):
        return self.files[item.file].text_lines[ln - 1]

    def find(self, key, short):
        """The item named `key`, or the only one named `short` in another module."""
        if key in self.items:
            return self.items[key]
        same = self.by_short.get(short, [])
        return same[0] if len(same) == 1 else None


def module_of(rel):
    parts = rel[:-3].split(os.sep)
    if parts[-1] in ('lib', 'main', 'mod'):
        parts = parts[:-1]
    return '::'.join(parts) or 'crate'


# ------------------------------------------------------------------------------------ diffing


def stat_cat(item, ln, involved, lemmas):
    """What line `ln` of `item` counts as: 'spec' or 'comment' (in the specification), or 'lemma',
    'proof', 'exec', 'other'."""
    cat = item.lines[ln]
    if cat == 'contract' or (cat == 'specfn' and involved) or (cat == 'lemma' and lemmas):
        return 'comment' if ln in item.comments else 'spec'
    return {'lemma': 'lemma', 'specfn': 'proof', 'proof': 'proof', 'exec': 'exec'}.get(cat, 'other')


def entries(crate, item, involved, opts):
    """The specification lines of an item: [(text, line)], blank lines left out."""
    show = {'spec', 'comment'} if opts.comments else {'spec'}
    return [(crate.line(item, ln), ln) for ln in sorted(item.lines)
            if crate.line(item, ln).strip() and stat_cat(item, ln, involved, opts.lemmas) in show]


def line_stats(crate_a, a, crate_b, b, involved, lemmas):
    """Per STATS category: (added, removed) non-blank lines."""
    def seqs(crate, item):
        s = collections.defaultdict(list)
        for ln in sorted(item.lines) if item else ():
            text = crate.line(item, ln).strip()
            if text:
                s[stat_cat(item, ln, involved, lemmas)].append(text)
        return s
    sa, sb = seqs(crate_a, a), seqs(crate_b, b)
    stats = {}
    for cat in STATS:
        x, y = sa.get(cat, []), sb.get(cat, [])
        add = rem = 0
        for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, x, y, autojunk=False).get_opcodes():
            if op != 'equal':
                rem += i2 - i1
                add += j2 - j1
        stats[cat] = (add, rem)
    return stats


def hunks(ea, eb, context, ignore_space):
    key = (lambda s: re.sub(r'\s+', '', s)) if ignore_space else (lambda s: s.rstrip())
    sm = difflib.SequenceMatcher(None, [key(e[0]) for e in ea], [key(e[0]) for e in eb], autojunk=False)
    for group in sm.get_grouped_opcodes(context):
        lines = []
        for op, i1, i2, j1, j2 in group:
            if op == 'equal':
                lines += [(' ', e) for e in eb[j1:j2]]
            else:
                lines += [('-', e) for e in ea[i1:i2]] + [('+', e) for e in eb[j1:j2]]
        yield (group[0][1], group[-1][2]), (group[0][3], group[-1][4]), lines


# ------------------------------------------------------------------------------------ clauses


def clause_diff(a, b):
    """Clauses of item b not in item a, and of a not in b (multisets of (keyword, tokens))."""
    ca = collections.Counter((c[0], c[2]) for c in a.clauses) if a else collections.Counter()
    cb = collections.Counter((c[0], c[2]) for c in b.clauses) if b else collections.Counter()
    added, removed = [], []
    left = cb - ca
    for c in b.clauses if b else ():
        if left[(c[0], c[2])]:
            left[(c[0], c[2])] -= 1
            added.append(c)
    left = ca - cb
    for c in a.clauses if a else ():
        if left[(c[0], c[2])]:
            left[(c[0], c[2])] -= 1
            removed.append(c)
    return added, removed


# ------------------------------------------------------------------------------------- report


class Link:
    def __init__(self, report_dir, base):
        self.report_dir, self.base = report_dir, base

    def __call__(self, crate, rel, first, last=None):
        path = os.path.join(crate.src, rel)
        last = first if last is None else last
        shown = os.path.relpath(path, self.base)
        lines = f'{first}' if first == last else f'{first}-{last}'
        anchor = f'#L{first}' if first == last else f'#L{first}-L{last}'
        return f'[{shown}:{lines}]({os.path.relpath(path, self.report_dir)}{anchor})'


def cell(s, limit=220):
    s = s if len(s) <= limit else s[:limit - 1] + '…'
    return '`' + s.replace('|', '\\|').replace('`', "'") + '`'


def pm(stat):
    add, rem = stat
    return f'+{add} −{rem}' if add or rem else '0'


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('original', help='the crate before the amendment (its root or its src/)')
    ap.add_argument('amended', help='the amended crate (its root or its src/)')
    ap.add_argument('--notes', default=os.path.join(HERE, 'amendment_notes.json'))
    ap.add_argument('--report', default=os.path.join(HERE, 'spec_diff_report.md'))
    ap.add_argument('--diff', help='the unified diff of the specifications (default: spec_diff.diff next '
                    'to the report)')
    ap.add_argument('--template', action='store_true',
                    help='add an empty note for each changed item that has none for its current version')
    ap.add_argument('--lemmas', action='store_true',
                    help='include the requires/ensures of proof functions in the specification')
    ap.add_argument('--comments', action='store_true', help='show comment lines inside the specification')
    ap.add_argument('-w', '--ignore-space', action='store_true', help='ignore changes in whitespace')
    ap.add_argument('--context', type=int, default=3, help='lines of context in a hunk (default 3)')
    args = ap.parse_args()
    args.diff = args.diff or os.path.join(os.path.dirname(os.path.abspath(args.report)), 'spec_diff.diff')

    a = Crate(args.original, 'ORIGINAL')
    b = Crate(args.amended, 'AMENDED')
    for crate in (a, b):
        crate.mark_involved(args.lemmas)

    # -- match items: same key first, then the same name in another module
    pairs = {key: a.items[key] for key in b.items if key in a.items}
    for key, ib in b.items.items():
        ia = None if key in pairs else a.find(key, ib.short)
        if ia is not None and ia.key not in b.items and ia not in pairs.values():
            pairs[key] = ia
    findings = [[pairs.get(key), ib] for key, ib in b.items.items()]
    matched = {id(ia) for ia in pairs.values()}
    findings += [[ia, None] for ia in a.items.values() if id(ia) not in matched]

    report_dir = os.path.dirname(os.path.abspath(args.report))
    link = Link(report_dir, os.path.commonpath([a.root, b.root]) if a.root != b.root
                else os.path.dirname(a.root))

    def counted(item):
        return item is not None and (item.mode != 'proof' or args.lemmas)

    results = []
    for ia, ib in findings:
        involved = bool((ia and ia.involved) or (ib and ib.involved))
        stats = line_stats(a, ia, b, ib, involved, args.lemmas)
        ea = entries(a, ia, involved, args) if ia else []
        eb = entries(b, ib, involved, args) if ib else []
        hs = list(hunks(ea, eb, args.context, args.ignore_space))
        if ia and ib and not hs and not any(x or y for x, y in stats.values()):
            continue
        status = 'changed' if ia and ib else 'added' if ib else 'removed'
        it = ib or ia
        f = dict(a=ia, b=ib, key=it.key, kind=it.kind, status=status, stats=stats, hunks=hs, ea=ea, eb=eb,
                 clauses=[], involved=involved,
                 spec=bool(hs) or stats['spec'] != (0, 0))
        added, removed = clause_diff(ia if counted(ia) else None, ib if counted(ib) else None)
        f['clauses'] = ([dict(sign='+', clause=c) for c in added]
                        + [dict(sign='−', clause=c) for c in removed])
        results.append(f)

    # -- notes
    doc = json.load(open(args.notes)) if os.path.exists(args.notes) else []
    notes = doc.get('items', []) if isinstance(doc, dict) else doc
    summary = doc.get('summary', '') if isinstance(doc, dict) else ''
    by_key = {e['key']: e for e in notes}
    for f in results:
        f['note'] = by_key.get(f['key'])
    if args.template:
        added_notes = 0
        for f in results:
            if f['note'] is None:
                e = dict(key=f['key'], value=[], clauses={}, agent_note='')
                notes.append(e)
                f['note'] = e
                added_notes += 1
        with open(args.notes, 'w') as fh:
            json.dump(dict(doc, items=notes) if isinstance(doc, dict) else notes, fh, indent=2,
                      ensure_ascii=False)
            fh.write('\n')
        print(f'{args.notes}: {added_notes} empty notes added')
    for f in results:
        note = f['note'] or {}
        kinds, by_text = note.get('value', []), note.get('clauses', {})
        default = by_text.get('*') or (kinds[0] if len(kinds) == 1 else None)
        for c in f['clauses']:
            if c['sign'] == '+':
                text = re.sub(r'\s+', ' ', c['clause'][1])
                c['value'] = next((k for frag, k in by_text.items()
                                   if frag != '*' and re.sub(r'\s+', ' ', frag) in text), default)
    changed = {f['key'] for f in results}
    orphans = [e for e in notes if e['key'] not in changed]

    order = {'changed': 0, 'added': 1, 'removed': 2}
    results.sort(key=lambda f: (order[f['status']], (f['b'] or f['a']).file, (f['b'] or f['a']).span[0]))
    write_report(args, a, b, results, summary, orphans, link)
    write_diff(args, a, b, results, link)
    n = collections.Counter(f['status'] for f in results if f['spec'])
    print(f"specification: {n['changed']} changed, {n['added']} added, {n['removed']} removed; "
          f"{sum(1 for f in results if not f['spec'])} other items changed")
    print(f'report: {args.report}\ndiff: {args.diff}')


def signature(crate, item):
    return crate.line(item, item.sig_line).strip() if item and item.sig_line else ''


def hunk_header(f, la, lb, i1, j1):
    ha = f"-{la[0]},{la[1] - la[0] + 1}" if la else f"-{f['ea'][i1 - 1][1] if i1 else 0},0"
    hb = f"+{lb[0]},{lb[1] - lb[0] + 1}" if lb else f"+{f['eb'][j1 - 1][1] if j1 else 0},0"
    return f'@@ {ha} {hb} @@'


def hunk_ranges(f, i1, i2, j1, j2):
    la = (f['ea'][i1][1], f['ea'][i2 - 1][1]) if i2 > i1 else None
    lb = (f['eb'][j1][1], f['eb'][j2 - 1][1]) if j2 > j1 else None
    return la, lb


def write_diff(args, a, b, results, link):
    """All the specification hunks as one unified diff, file by file."""
    out = ['Specification diff (spec_diff.py): requires/ensures clauses and the spec functions they use'
           + (', with lemmas' if args.lemmas else '') + '. Line numbers are those of the source files;',
           'each hunk header ends with the signature of its function.', '']
    by_file = collections.OrderedDict()
    for f in sorted((f for f in results if f['hunks']),
                    key=lambda f: ((f['b'] or f['a']).file, (f['b'] or f['a']).span[0])):
        by_file.setdefault((f['b'] or f['a']).file, []).append(f)
    for rel, fs in by_file.items():
        pa = os.path.relpath(os.path.join(a.src, rel), link.base)
        pb = os.path.relpath(os.path.join(b.src, rel), link.base)
        out += [f'--- {pa}', f'+++ {pb}']
        for f in fs:
            sig = signature(b, f['b']) or signature(a, f['a'])
            for (i1, i2), (j1, j2), lines in f['hunks']:
                la, lb = hunk_ranges(f, i1, i2, j1, j2)
                out.append(hunk_header(f, la, lb, i1, j1) + (f' {sig}' if sig else ''))
                out += [f'{sign}{e[0]}'.rstrip() for sign, e in lines]
    with open(args.diff, 'w') as fh:
        fh.write('\n'.join(out) + '\n')


def write_report(args, a, b, results, summary, orphans, link):
    report_dir = os.path.dirname(os.path.abspath(args.report))
    rel = lambda crate: os.path.relpath(crate.root, report_dir)
    spec = [f for f in results if f['spec']]
    other = [f for f in results if not f['spec']]
    out = []
    w = out.append
    w('# Specification amendments\n')
    w('Generated by `spec_diff.py`. The *specification* is the `requires` and `ensures` clauses of the functions '
      + ('' if args.lemmas else 'that are not proof functions ')
      + '(executable functions, trait method declarations, `assume_specification`'
      + (', lemmas' if args.lemmas else '') + '), and the spec functions they use, directly or through other '
      'spec functions. '
      + ('Comment lines inside it are shown. ' if args.comments else 'Comments are left out. ')
      + 'Each item of the amended crate is matched by name with the same item of the original crate, and their '
      'specification lines are compared with a classic line-by-line diff. Hunk headers give the line numbers '
      'in the source files and end with the function\'s signature, as `diff -p` does. Every hunk is also in '
      f"[`{os.path.relpath(args.diff, report_dir)}`]({os.path.relpath(args.diff, report_dir)}). Changes outside "
      f"the specification ({'' if args.lemmas else 'lemmas, '}proofs, imports, documentation, executable code) "
      'are counted, and listed '
      'under [Other changes](#other-changes-outside-the-specification), but not diffed.')
    w('\nA *clause* is one comma-separated expression after `requires` or `ensures`. Each item lists the '
      'clauses that the amendment adds or removes, compared token by token (up to the name of the result and '
      'trailing commas), with the kind the notes give them.')
    w('')
    w(f'- Original: `{rel(a)}`')
    w(f'- Amended: `{rel(b)}`')
    noted = sum(1 for f in results if f['note'] and (f['note'].get('agent_note') or f['note'].get('value')))
    w(f'- Notes: `{os.path.relpath(args.notes, report_dir)}` ({noted} of {len(results)} changed items explained)')
    w('')

    if summary:
        w('## Conclusions (from the notes)\n')
        w((summary if isinstance(summary, str) else '\n'.join(summary)).strip() + '\n')

    # -- summary
    n = collections.Counter(f['status'] for f in spec)
    w('## Summary\n')
    w('| items | count |')
    w('|---|---|')
    for st in ('changed', 'added', 'removed'):
        w(f'| specification {st} | {n[st]} |')
    w(f'| other changes only | {len(other)} |')
    w('')
    tot = {c: [0, 0] for c in STATS}
    for f in results:
        for c, (x, y) in f['stats'].items():
            tot[c][0] += x
            tot[c][1] += y
    w('| lines (non-blank) | added | removed |')
    w('|---|---|---|')
    for c, label in (('spec', '**specification** (diffed)'),
                     ('comment', 'comments inside the specification' + ('' if args.comments else ' (not shown)')),
                     ('lemma', 'lemma requires/ensures'), ('proof', 'proof code, and spec functions used only by proofs'),
                     ('exec', 'executable code'), ('other', 'other (signatures, imports, documentation, comments)')):
        if c == 'lemma' and args.lemmas:
            continue
        w(f'| {label} | {tot[c][0]} | {tot[c][1]} |')
    w('')
    cl = [c for f in results for c in f['clauses']]
    add = sum(1 for c in cl if c['sign'] == '+')
    w(f'Clauses: **{add} added**, **{len(cl) - add} removed**.\n')

    # -- value
    vals = collections.defaultdict(list)
    for f in results:
        for v in (f['note'] or {}).get('value', []):
            vals[v].append(f)
    if vals:
        w('### Value, by kind (from the notes)\n')
        w('Items: the changed items of that kind, in the specification + outside it (an item can have several '
          'kinds). Clauses: the added clauses of that kind. *Reference*: the specification the amendment was '
          'checked against.\n')
        w('| kind | meaning | items | clauses added |')
        w('|---|---|---|---|')
        added = [c for f in results for c in f['clauses'] if c['sign'] == '+']
        for v in list(VALUE_KINDS) + sorted(set(vals) - set(VALUE_KINDS)):
            fs = vals.get(v, [])
            if not fs:
                continue
            w(f"| {v} | {VALUE_KINDS.get(v, '(not a known kind)')} | "
              f"{sum(1 for f in fs if f['spec'])} + {sum(1 for f in fs if not f['spec'])} | "
              f"{sum(1 for c in added if c.get('value') == v)} |")
        unknown = sum(1 for c in added if not c.get('value'))
        if unknown:
            w(f'| (none) | added clauses that no note classifies | | {unknown} |')
        w('')

    # -- overview
    w('### Items whose specification changed\n')
    w('| item | kind | status | specification lines | clauses (added / removed) | value |')
    w('|---|---|---|---|---|---|')
    for f in spec:
        k = collections.Counter(c['sign'] for c in f['clauses'])
        clauses = f"{k['+']} / {k['−']}" if f['clauses'] else ''
        w(f"| `{f['key']}` | {f['kind']} | {f['status']} | {pm(f['stats']['spec'])} | {clauses} | "
          f"{', '.join((f['note'] or {}).get('value', []))} |")
    w('')

    # -- items
    titles = {'changed': 'Changed', 'added': 'Added (not in the original)',
              'removed': 'Removed (not in the amended crate)'}
    for st in ('changed', 'added', 'removed'):
        fs = [f for f in spec if f['status'] == st]
        if fs:
            w(f'## {titles[st]}\n')
            for f in fs:
                write_item(w, f, a, b, link)

    # -- other changes
    if other:
        w('## Other changes (outside the specification)\n')
        w('Changed items whose specification lines did not change: not diffed. Lines added / removed, by kind.\n')
        for f in other:
            it = f['b'] or f['a']
            s = f['stats']
            counts = ', '.join(f'{c} {pm(s[c])}' for c in ('lemma', 'proof', 'exec', 'other', 'comment')
                               if s[c] != (0, 0))
            locs = ' · '.join(([f"original {link(a, f['a'].file, *f['a'].span)}"] if f['a'] else [])
                              + ([f"amended {link(b, f['b'].file, *f['b'].span)}"] if f['b'] else []))
            note = f['note'] or {}
            value = f" — **{', '.join(note['value'])}**" if note.get('value') else ''
            expl = f": {note['agent_note']}" if note.get('agent_note') else ''
            w(f"- `{f['key']}` ({it.kind}, {f['status']}; {counts}; {locs}){value}{expl}")
        w('')

    if orphans:
        w('## Notes on items that did not change\n')
        for e in orphans:
            w(f"- `{e['key']}`: {e.get('agent_note', '')[:200]}")
        w('')
    with open(args.report, 'w') as fh:
        fh.write('\n'.join(out).rstrip() + '\n')


def write_item(w, f, a, b, link):
    ia, ib = f['a'], f['b']
    it = ib or ia
    w(f"### `{f['key']}`\n")
    s = f['stats']
    outside = ', '.join(f'{c} {pm(s[c])}' for c in ('comment', 'lemma', 'proof', 'exec', 'other') if s[c] != (0, 0))
    head = [f"Kind: {f['kind']}" + (f" (trusted: {', '.join(sorted(it.trusted))})" if it.trusted else '')
            + f" · specification lines {pm(s['spec'])}" + (f' · not diffed: {outside}' if outside else '')]
    note = f['note']
    if note and note.get('value'):
        head.append('Value: ' + ', '.join(f'**{v}**' for v in note['value']))
    if note and note.get('agent_note'):
        head.append(f"Explanation: {note['agent_note']}")
    if ia:
        head.append(f'Original: {link(a, ia.file, *ia.span)}')
    if ib:
        head.append(f'Amended: {link(b, ib.file, *ib.span)}')
    w('  \n'.join(head) + '\n')
    if f['clauses']:
        w('| | clause | value |')
        w('|---|---|---|')
        for c in f['clauses']:
            kw, text, _, l1, l2 = c['clause']
            crate, item = (b, ib) if c['sign'] == '+' else (a, ia)
            w(f"| {c['sign']} {kw} {link(crate, item.file, l1, l2)} | {cell(text)} | {c.get('value') or ''} |")
        w('')
    pa = os.path.relpath(os.path.join(a.src, it.file), link.base)
    pb = os.path.relpath(os.path.join(b.src, it.file), link.base)
    sig = signature(b, ib) or signature(a, ia)
    for (i1, i2), (j1, j2), lines in f['hunks']:
        la, lb = hunk_ranges(f, i1, i2, j1, j2)
        locs = ([f'Original {link(a, ia.file, *la)}'] if la else []) + ([f'Amended {link(b, ib.file, *lb)}'] if lb else [])
        w(' · '.join(locs) + '\n')
        w('```diff')
        w(f'--- {pa}' if ia else '--- /dev/null')
        w(f'+++ {pb}' if ib else '+++ /dev/null')
        w(hunk_header(f, la, lb, i1, j1) + (f' {sig}' if sig else ''))
        for sign, e in lines:
            w(f'{sign}{e[0]}'.rstrip())
        w('```\n')


if __name__ == '__main__':
    main()
