#!/usr/bin/env python3
"""Structural check of the Lean-emitted C (bridge/.lake/build/ir/GenDemo.c): every generic .view() call site's
specialized per-element loop (and the specialized groupFold insert it calls) contains no lean_apply_* (indirect
closure call) and no lean_alloc_closure. Reports per-function counts of allocations / calls. Exit 1 on violation."""
import re, sys
from collections import Counter
s = open(sys.argv[1]).read()
def body(fn):
    m = re.search(r'^LEAN_EXPORT [^\n]*\b' + re.escape(fn) + r'\([^)]*\) \{\n', s, re.M)
    if not m: return None
    d = 0
    for j in range(m.end() - 2, len(s)):
        if s[j] == '{': d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0: return s[m.start():j + 1]
names = sorted(set(re.findall(r'^LEAN_EXPORT lean_object\* (l_(?:List_foldl___at_view[A-Za-z]+___spec__\d+(?:___at_view[A-Za-z]+___spec__\d+)?|Vw_gInsK___at_view[A-Za-z]+___spec__\d+))\(', s, re.M)))
bad = 0
for site in ["viewA", "viewAi", "viewAp", "viewB", "viewBi", "viewBp"]:
    fs = [n for n in names if re.search(r'_at_' + site + r'___spec', n)]
    if not fs: print("MISSING specialized loop for", site); bad += 1
    for fn in fs:
        b = body(fn)
        c = Counter(re.findall(r'(lean_apply_\d+|lean_alloc_closure|lean_alloc_ctor|lean_string_dec_eq|\bl_[A-Za-z0-9_]+(?=\())', b))
        c.pop(fn, None)
        ind = sum(v for k, v in c.items() if k.startswith('lean_apply') or k == 'lean_alloc_closure')
        if ind: bad += 1
        print(f"{site:7s} {fn:60s} indirect={ind} {dict(c)}")
print(f"SPEC_CHECK sites=6 violations={bad}")
sys.exit(1 if bad else 0)
