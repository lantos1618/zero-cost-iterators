#!/usr/bin/env python3
"""Parse SIFT10K (siftsmall) fvecs/ivecs, verify shape and integrality, write raw uint8/int32 blobs. Fail closed."""
import struct, sys, os
D = "work/data"
def fvecs(path, want_n, want_d):
    b = open(path, "rb").read()
    rec = 4 + 4 * want_d
    if len(b) != want_n * rec: sys.exit("FAIL %s: size %d != %d*%d" % (path, len(b), want_n, rec))
    out = bytearray(); nonint = outside = 0
    for r in range(want_n):
        d, = struct.unpack_from("<i", b, r * rec)
        if d != want_d: sys.exit("FAIL %s row %d: dim %d" % (path, r, d))
        for v in struct.unpack_from("<%df" % d, b, r * rec + 4):
            if v != int(v): nonint += 1; continue
            if not (0 <= v <= 255): outside += 1; continue
            out.append(int(v))
    if nonint or outside: sys.exit("FAIL %s: %d non-integer, %d outside [0,255] coordinates" % (path, nonint, outside))
    print("%s: %d rows x %d dims, all %d coordinates exact integers in [0,255] (min %d max %d)" % (path, want_n, want_d, len(out), min(out), max(out)))
    return out
def ivecs(path, want_n, want_k):
    b = open(path, "rb").read(); rec = 4 + 4 * want_k
    if len(b) != want_n * rec: sys.exit("FAIL %s: size" % path)
    out = []
    for r in range(want_n):
        k, = struct.unpack_from("<i", b, r * rec)
        if k != want_k: sys.exit("FAIL %s row %d: k %d" % (path, r, k))
        ids = struct.unpack_from("<%di" % k, b, r * rec + 4)
        if any(not (0 <= i < 10000) for i in ids): sys.exit("FAIL %s: id out of range" % path)
        out += ids
    print("%s: %d rows x %d neighbour ids in [0,10000)" % (path, want_n, want_k))
    return out
q = fvecs(os.path.join(D, "siftsmall_query.fvecs"), 100, 128)
x = fvecs(os.path.join(D, "siftsmall_base.fvecs"), 10000, 128)
g = ivecs(os.path.join(D, "siftsmall_groundtruth.ivecs"), 100, 100)
open(os.path.join(D, "q.u8"), "wb").write(q)
open(os.path.join(D, "x.u8"), "wb").write(x)
open(os.path.join(D, "gt.i32"), "wb").write(struct.pack("<%di" % len(g), *g))
