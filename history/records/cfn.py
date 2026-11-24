import re, sys
from collections import Counter
s=open(sys.argv[1]).read()
def body(fn):
    m=re.search(r'^LEAN_EXPORT [^\n]*\b'+re.escape(fn)+r'\([^)]*\) \{\n', s, re.M)
    if not m: return None
    i=m.end()-2; d=0
    for j in range(i,len(s)):
        if s[j]=='{': d+=1
        elif s[j]=='}':
            d-=1
            if d==0: return s[m.start():j+1]
for fn in sys.argv[2:]:
    b=body(fn)
    if not b: print('MISSING',fn); continue
    calls=re.findall(r'(lean_apply_\d|lean_alloc_ctor|lean_alloc_closure|lean_string_dec_eq|lean_nat_\w+|lean_is_exclusive|lean_ctor_release|\bl_\w+(?=\())',b)
    print('===',fn,len(b.splitlines()),'lines', dict(Counter(calls)))
