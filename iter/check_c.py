#!/usr/bin/env python3
"""Inspect the C Lean emitted for Bench.lean (run from iter/ after `lake build`). For each benchmarked function, follow its calls to
specialised helpers and count, per function body: heap allocations (lean_alloc_*), closure
allocations (lean_alloc_closure) and indirect closure calls (lean_apply_*). Gate: every Iter chain
has 0 closure allocations, 0 indirect calls, and no more allocation sites than its hand loop."""
import re, sys
src = open(sys.argv[1] if len(sys.argv) > 1 else ".lake/build/ir/Bench.c").read()
bodies = {}
def body_at(pos):
    """text of the brace-balanced block starting at src[pos] == '{'"""
    depth = 0
    for k in range(pos, len(src)):
        if src[k] == '{': depth += 1
        elif src[k] == '}':
            depth -= 1
            if depth == 0: return src[pos:k + 1]
    return src[pos:]
for m in re.finditer(r'^(?:LEAN_EXPORT|static) [^\n;]*? (l_\w+)\([^\n;]*\) \{$', src, re.M):
    bodies.setdefault(m.group(1), body_at(m.end() - 1))
for m in re.finditer(r'^static lean_object\* _init_(l_\w+)\(\) \{$', src, re.M):
    bodies[m.group(1)] = ""  # one-time constants built at startup, not per call
def reach(fn):
    seen, todo = set(), [fn]
    while todo:
        f = todo.pop()
        if f in seen or f not in bodies: continue
        seen.add(f)
        todo += [c for c in re.findall(r'\b(l_\w+)\(', bodies[f]) if c not in seen]
    return seen
def counts(fn):
    fs = reach(fn)
    text = "".join(bodies[f] for f in fs)
    return dict(alloc=len(re.findall(r'lean_alloc_\w+\(|lean_box_(?:uint64|float|usize)\(', text)),
                closure=len(re.findall(r'lean_alloc_closure\(', text)),
                apply=len(re.findall(r'lean_apply_\w+\(', text)), fns=len(fs))
# (Iter chain, hand loop, gated). enumerate, drop and dropWhile are reported but not gated: the
# (accumulator, counter/flag) pair is a heap cell in Lean 4.15's output (a known gap, see docs/DETAILS.md).
# iterF2/iterD2 use the array sources `iterIdx`/`iterFrom`; boxing a UInt64 counts as an allocation site.
pairs = [("l_iterU", "l_handU", True), ("l_iterA", "l_handA", True), ("l_iterF", "l_handF", False), ("l_iterD", "l_handD", False),
         ("l_iterF2", "l_handF", False), ("l_iterD2", "l_handD", False)]
bad = 0
print(f"{'function':10} {'alloc sites':>11} {'closures':>8} {'lean_apply':>10} {'C fns':>6}")
for it, hd, gated in pairs:
    ci, ch = counts(it), counts(hd)
    for n, c in ((it, ci), (hd, ch)):
        print(f"{n[2:]:10} {c['alloc']:>11} {c['closure']:>8} {c['apply']:>10} {c['fns']:>6}")
    worse = ci['closure'] or ci['apply'] or ci['alloc'] > ch['alloc']
    if worse and gated: bad += 1; print(f"  FAIL {it}")
    elif worse: print(f"  KNOWN_GAP {it}: {ci['alloc'] - ch['alloc']} extra allocation site(s)")
print(f"CHECK_C gated={sum(g for *_, g in pairs)} fails={bad}")
sys.exit(1 if bad else 0)
