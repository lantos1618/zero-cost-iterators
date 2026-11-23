#!/usr/bin/env python3
"""Independent, fail-closed validator for ONE emitted C file (does not import gen.py).
  check_c.py FILE.c [IR.json]
1. Buffer scan over the C tokens: any allocation API, array declaration (stack/VLA/static),
   pointer declaration, subscript other than the reads a[i]/b[i], or store through a subscript/
   pointer other than the single final `*out = acc;` is a BUFFER finding.
2. Lift: every statement must match one whitelisted template, else REJECT (unknown construct).
   Templates map back to IR ops; with IR.json the lifted program must equal the IR exactly.
Exit: 0 PASS (no buffer, lifted, equal to IR if given), 1 BUFFER, 2 REJECT (unrecognised), 3 IR MISMATCH."""
import re, sys, json

def strip(src):
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
    return re.sub(r"//[^\n]*", "", src)

INCLUDES = {"#include <stddef.h>", "#include <stdint.h>", "#define I8DOT_MAX_N 131071u"}
SIG = "int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {"
STMT = {  # exact statement text -> lifted meaning
    "if (n > I8DOT_MAX_N) return -1;": ("guard",),
    "int32_t acc = 0;": ("decl",), "int32_t r0 = 0;": ("decl",), "int32_t r1 = 0;": ("decl",),
    "r0 = (int32_t)a[i];": ("op", "LdA"), "r1 = (int32_t)b[i];": ("op", "LdB"),
    "r0 = r0 * r1;": ("op", "Mul"), "acc = acc + r0;": ("op", "Acc"),
    "acc = (int32_t)((uint32_t)acc & 0xFFu);": ("wrap1",),
    "if (acc > 127) acc = acc - 256;": ("wrap2",),
    "for (size_t i = 0; i < n; i++) {": ("for",), "}": ("end",),
    "*out = acc;": ("out",), "return 0;": ("ret",),
}

def buffer_findings(lines):
    f = []
    for no, l in lines:
        body = l
        if re.search(r"\b(malloc|calloc|realloc|alloca|free|aligned_alloc|new|memcpy|memset)\b", body):
            f.append((no, "allocation/bulk-memory API", l))
        if re.search(r"#include\s*<(stdlib|alloca|string|malloc)\.h>", body):
            f.append((no, "allocation header", l))
        if re.search(r"\bstatic\b", body):
            f.append((no, "static storage", l))
        if l != SIG:
            if re.search(r"\b(int|int8_t|int16_t|int32_t|int64_t|uint8_t|uint16_t|uint32_t|uint64_t|long|short|char|size_t|float|double)\b[^;=()]*\[", body):
                f.append((no, "array declaration (stack/VLA)", l))
            if re.search(r"\b(int|int8_t|int16_t|int32_t|int64_t|uint8_t|uint16_t|uint32_t|uint64_t|long|short|char|size_t|float|double|void)\b\s*\*", body):
                f.append((no, "pointer declaration/cast", l))
            for m in re.finditer(r"(\w+)\s*\[([^\]]*)\]", body):
                if (m.group(1), m.group(2).strip()) not in {("a", "i"), ("b", "i")}:
                    f.append((no, "subscript %s[%s]" % (m.group(1), m.group(2)), l))
            if re.search(r"\]\s*=[^=]", body):
                f.append((no, "store through subscript", l))
            if re.match(r"\*\s*\w+\s*=[^=]", body) and l != "*out = acc;":
                f.append((no, "store through pointer", l))
    return f

def main():
    path = sys.argv[1]
    lines = [(i + 1, l.strip()) for i, l in enumerate(strip(open(path).read()).split("\n")) if l.strip()]
    print("file:", path)
    bf = buffer_findings(lines)
    unknown, prog, cur, depth, guard, outs, sig = [], [], None, 0, 0, 0, 0
    pending_wrap = False
    for no, l in lines:
        if l in INCLUDES:
            continue
        if l == SIG:
            sig += 1; depth = 1; continue
        k = STMT.get(l)
        if k is None or depth == 0:
            unknown.append((no, l)); continue
        if pending_wrap and k != ("wrap2",):
            unknown.append((no, "wrap without its sign-fix line")); pending_wrap = False
        if k == ("for",):
            if cur is not None: unknown.append((no, "nested loop"))
            cur = []; depth += 1
        elif k == ("end",):
            depth -= 1
            if cur is not None and depth == 1:
                prog.append({"loop": cur}); cur = None
        elif k[0] == "op":
            if cur is None: unknown.append((no, "op outside loop: " + l))
            else: cur.append(k[1])
        elif k == ("wrap1",):
            pending_wrap = True
        elif k == ("wrap2",):
            if not pending_wrap or cur is None: unknown.append((no, "stray wrap line"))
            else: cur.append("Wrap"); pending_wrap = False
        elif k == ("guard",):
            if prog or cur is not None: unknown.append((no, "guard after loop"))
            guard += 1
        elif k == ("out",):
            outs += 1
    if sig != 1: unknown.append((0, "expected exactly one i8dot definition, found %d" % sig))
    if guard != 1: unknown.append((0, "length guard n <= 131071 missing or repeated"))
    if outs != 1: unknown.append((0, "expected exactly one *out = acc"))
    loops = len(prog)
    la = sum(l["loop"].count("LdA") for l in prog); lb = sum(l["loop"].count("LdB") for l in prog)
    print("loops=%d  loads_a_per_elem=%d  loads_b_per_elem=%d" % (loops, la, lb))
    for no, why, l in bf:
        print("BUFFER line %d: %s :: %s" % (no, why, l))
    for no, l in unknown:
        print("UNRECOGNISED line %d: %s" % (no, l))
    if bf:
        print("VERDICT: BUFFER (intermediate materialization found in emitted C)"); sys.exit(1)
    if unknown:
        print("VERDICT: REJECT (fail-closed: construct outside the validated subset)"); sys.exit(2)
    print("lifted IR:", json.dumps(prog))
    if len(sys.argv) > 2:
        ir = json.load(open(sys.argv[2]))["prog"]
        if ir != prog:
            print("VERDICT: IR MISMATCH vs", sys.argv[2], json.dumps(ir)); sys.exit(3)
        print("lifted IR == %s" % sys.argv[2])
    print("VERDICT: PASS (no intermediate buffer; single-pass shape: %s)" % (loops == 1 and la == 1 and lb == 1))
    sys.exit(0)

main()
