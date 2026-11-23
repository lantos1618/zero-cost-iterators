#!/usr/bin/env python3
"""Independent, fail-closed validator for ONE emitted C file (does not import gen.py).

  check_c.py --gate nobuf FILE.c              no intermediate buffer (and FILE parses)
  check_c.py --gate exact FILE.c PROVED.json  FILE lifts to exactly the IR whose Bend PROOF passed
  check_c.py --gate match FILE.c IR.json      emitter consistency: FILE lifts to exactly IR.json

Lexical gate (on the raw bytes, comments included): no backslash (line splice), no "??"
(trigraphs), every block comment opens and closes on one line. Comments are then removed by a
left-to-right scan, lines are stripped, empty lines dropped.

Grammar (complete, ordered; each item is one exact line; nothing else is accepted):
  file   := "#include <stddef.h>" "#include <stdint.h>" "#define I8DOT_MAX_N 131071u"
            SIG GUARD "int32_t acc = 0;" "int32_t r0 = 0;" "int32_t r1 = 0;"
            loop+ "*out = acc;" "return 0;" "}" EOF
  loop   := "for (size_t i = 0; i < n; i++) {" item+ "}"
  item   := "r0 = (int32_t)a[i];"            -> LdA
          | "r1 = (int32_t)b[i];"            -> LdB
          | "r0 = r0 * r1;"                  -> Mul
          | "acc = acc + r0;"                -> Acc
          | "acc = (int32_t)((uint32_t)acc & 0xFFu);" "if (acc > 127) acc = acc - 256;"  -> Wrap
  SIG    := "int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {"
  GUARD  := "if (n > I8DOT_MAX_N) return -1;"
Exit: 0 PASS, 1 BUFFER (nobuf gate), 2 REJECT (lexical/grammar), 3 IR MISMATCH."""
import re, sys, json

HDR = ["#include <stddef.h>", "#include <stdint.h>", "#define I8DOT_MAX_N 131071u"]
SIG = "int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {"
GUARD = "if (n > I8DOT_MAX_N) return -1;"
DECLS = ["int32_t acc = 0;", "int32_t r0 = 0;", "int32_t r1 = 0;"]
FOR = "for (size_t i = 0; i < n; i++) {"
OPS = {"r0 = (int32_t)a[i];": "LdA", "r1 = (int32_t)b[i];": "LdB",
       "r0 = r0 * r1;": "Mul", "acc = acc + r0;": "Acc"}
WRAP = ("acc = (int32_t)((uint32_t)acc & 0xFFu);", "if (acc > 127) acc = acc - 256;")
TAIL = ["*out = acc;", "return 0;", "}"]

class Reject(Exception):
    pass

def lex(raw):
    for no, l in enumerate(raw.split("\n"), 1):
        if "\\" in l: raise Reject("line %d: backslash (line splice/escape) not allowed" % no)
        if "??" in l: raise Reject("line %d: '??' (trigraph) not allowed" % no)
    out, i = [], 0
    while i < len(raw):
        if raw.startswith("/*", i):
            j = raw.find("*/", i + 2)
            if j < 0: raise Reject("unterminated block comment")
            if "\n" in raw[i:j]: raise Reject("block comment spans lines (line %d)" % (raw.count("\n", 0, i) + 1))
            out.append(" "); i = j + 2
        elif raw.startswith("//", i):
            j = raw.find("\n", i); i = len(raw) if j < 0 else j
        else:
            out.append(raw[i]); i += 1
    return [(no, l.strip()) for no, l in enumerate("".join(out).split("\n"), 1) if l.strip()]

def buffer_findings(lines):
    T = r"\b(int|int8_t|int16_t|int32_t|int64_t|uint8_t|uint16_t|uint32_t|uint64_t|long|short|char|size_t|float|double|void)\b"
    f = []
    for no, l in lines:
        if re.search(r"\b(malloc|calloc|realloc|alloca|free|aligned_alloc|new|memcpy|memset)\b", l): f.append((no, "allocation/bulk-memory API", l))
        if re.search(r"#include\s*<(stdlib|alloca|string|malloc)\.h>", l): f.append((no, "allocation header", l))
        if re.search(r"\bstatic\b", l): f.append((no, "static storage", l))
        if l == SIG: continue
        if re.search(T + r"[^;=()]*\[", l): f.append((no, "array declaration (stack/VLA/static)", l))
        if re.search(T + r"\s*\*", l): f.append((no, "pointer declaration/cast", l))
        for m in re.finditer(r"(\w+)\s*\[([^\]]*)\]", l):
            if (m.group(1), m.group(2).strip()) not in {("a", "i"), ("b", "i")}: f.append((no, "subscript %s[%s]" % (m.group(1), m.group(2)), l))
        if re.search(r"\]\s*=[^=]", l): f.append((no, "store through subscript", l))
        if re.match(r"\*\s*\w+\s*=[^=]", l) and l != "*out = acc;": f.append((no, "store through pointer", l))
    return f

def parse(lines):
    pos = [0]
    def peek():
        return lines[pos[0]] if pos[0] < len(lines) else (0, "<EOF>")
    def expect(want, what):
        no, l = peek()
        if l != want: raise Reject("line %d: expected %s %r, found %r" % (no, what, want, l))
        pos[0] += 1
    for h in HDR: expect(h, "header")
    expect(SIG, "signature"); expect(GUARD, "length guard")
    for d in DECLS: expect(d, "scalar declaration")
    prog = []
    while peek()[1] == FOR:
        pos[0] += 1; body = []
        while True:
            no, l = peek()
            if l in OPS: body.append(OPS[l]); pos[0] += 1
            elif l == WRAP[0]: pos[0] += 1; expect(WRAP[1], "wrap sign-fix"); body.append("Wrap")
            elif l == "}": pos[0] += 1; break
            else: raise Reject("line %d: expected loop-body statement or '}', found %r" % (no, l))
        if not body: raise Reject("empty loop body")
        prog.append({"loop": body})
    if not prog: raise Reject("line %d: expected %r, found %r" % (peek()[0], FOR, peek()[1]))
    expect(TAIL[0], "final output store (after the last loop)")
    expect(TAIL[1], "terminal return"); expect(TAIL[2], "closing brace")
    if pos[0] != len(lines): raise Reject("line %d: trailing content %r" % peek())
    return prog

def main():
    gate, path = sys.argv[2], sys.argv[3]
    assert sys.argv[1] == "--gate" and gate in ("nobuf", "exact", "match")
    print("gate=%s file=%s" % (gate, path))
    try:
        lines = lex(open(path).read())
        if gate == "nobuf":
            bf = buffer_findings(lines)
            for no, why, l in bf: print("BUFFER line %d: %s :: %s" % (no, why, l))
            if bf:
                print("VERDICT: BUFFER (intermediate materialization in emitted C)"); sys.exit(1)
        prog = parse(lines)
    except Reject as e:
        print("REJECT:", e); print("VERDICT: REJECT (fail-closed: outside the validated grammar)"); sys.exit(2)
    print("lifted IR:", json.dumps(prog))
    print("loops=%d  per-loop loads a/b: %s" % (len(prog), [(l["loop"].count("LdA"), l["loop"].count("LdB")) for l in prog]))
    if gate == "nobuf":
        print("VERDICT: PASS (parses; no intermediate buffer)"); sys.exit(0)
    ir = json.load(open(sys.argv[4]))["prog"]
    if ir != prog:
        print("VERDICT: IR MISMATCH vs %s %s" % (sys.argv[4], json.dumps(ir))); sys.exit(3)
    print("VERDICT: PASS (lifted IR == %s)" % sys.argv[4]); sys.exit(0)

main()
