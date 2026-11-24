#!/usr/bin/env python3
"""Medians/IQR/min-max per cell, gen/hand median ratio, strict 5% verdict. Primary = gcc -O3 (fixed before timing)."""
import csv, glob, os, sys, statistics as st
out = sys.argv[1]; K = ["dot", "l1", "l2", "ham", "osl"]
def q(v, p):
    v = sorted(v); x = (len(v) - 1) * p; i = int(x); return v[i] + (v[min(i + 1, len(v) - 1)] - v[i]) * (x - i)
cfgs = sorted({os.path.basename(f)[4:-6] for f in glob.glob(out + "/raw_*.csv")}, key=lambda c: (c != "gcc_O3", c))
res = {}
print("cfg layout kernel | gen median [IQR] (min-max) ms | hand median [IQR] (min-max) ms | ratio | signed% | strict")
for c in cfgs:
    for L in "AB":
        d = {}
        for r in csv.DictReader(open("%s/raw_%s_%s.csv" % (out, c, L))): d.setdefault((r["kernel"], r["form"]), []).append(float(r["ms"]))
        for k in K:
            g, h = d[(k, "gen")], d[(k, "hand")]; mg, mh = st.median(g), st.median(h); ratio = mg / mh
            ok = 0.95 <= ratio <= 1.05; res[(c, L, k)] = (ratio, ok)
            fmt = lambda v, m: "%.3f [%.3f] (%.3f-%.3f)" % (m, q(v, .75) - q(v, .25), min(v), max(v))
            print("%-18s %s %-4s | %s | %s | %.4f | %+.2f%% | %s%s" % (c, L, k, fmt(g, mg), fmt(h, mh), ratio, (ratio - 1) * 100,
                  "PASS" if ok else "MISS", "" if ok else (" (generated faster)" if ratio < 0.95 else " (generated slower)")))
print("\nper-config verdict (layout-sensitive = passes in one layout only):")
for c in cfgs:
    for k in K:
        a, b = res[(c, "A", k)][1], res[(c, "B", k)][1]
        print("%-18s %-4s A=%s B=%s%s" % (c, k, "PASS" if a else "MISS", "PASS" if b else "MISS", "  LAYOUT-SENSITIVE" if a != b else ""))
    n = sum(res[(c, L, k)][1] for L in "AB" for k in K)
    print("%-18s %d/10 kernel-layout cells within 5%%" % (c, n))
allp = all(res[("gcc_O3", L, k)][1] for L in "AB" for k in K)
rs = [res[(c, L, k)][0] for c in cfgs for L in "AB" for k in K]
print("\nratio range over all configs: %.4f .. %.4f" % (min(rs), max(rs)))
print("PRIMARY (gcc -O3, both layouts) ALL-FIVE 5%% TARGET: %s" % ("MET" if allp else "NOT MET"))
