#!/usr/bin/env python3
"""bend2lean.py: narrow, fail-closed, syntax-directed translation of the restricted Bend 2 subset used
by kernel.bend (+ a fixed whitelist of base.bend Nat/Cmp/Pair defs) and generated prog.bend files
into Lean 4 definitions. TRUSTED (unverified) component; see README. Exit 2 on anything unsupported.

  bend2lean.py kernel BASE.bend KERNEL.bend OUT.lean
  bend2lean.py progs  OUT.lean NAME=PROG.bend ...

Construct mapping (each is a trusted identification):
  type T is Data: C{f: A, ...}   -> inductive T | C (f : A) ...           (Bool -> Lean Bool, Nat -> Lean Nat)
  def f(+x: A, -y: B, z: C) -> R -> def f (x : A) (y : B) (z : C) : R    (+/- linearity/erasure marks dropped)
  match a b: case P Q: E         -> match a, b with | P, Q => E
  (a, b) = e  NEWLINE  E         -> let (a, b) := e; E
  Kn / Kn+e  (pattern or expr)   -> K / e + K     (Nat literal / K-fold Succ)
  C{e, ...}                      -> T.C e ...     (True{}/False{} -> true/false)
  f(e, ...) / f()                -> f e ... / f   ("." in names -> "_"; prog.bend "K." prefix dropped)
  (e1, e2) / A & B               -> (e1, e2) / A × B
"""
import re, sys, hashlib

BASE_WHITELIST = ["Cmp", "Pair.fst", "Pair.snd", "Cmp.is_lt", "Cmp.is_eq", "Cmp.is_le",
                  "Nat.add", "Nat.sub", "Nat.mul", "Nat.divmod.go", "Nat.divmod", "Nat.cmp", "Nat.is_lt", "Nat.is_eq", "Nat.is_le", "Nat.mod"]
IDENT = r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*"

class Unsupported(Exception):
    pass

def die(msg):
    raise Unsupported(msg)

def lname(n):
    if n.startswith("K."):
        n = n[2:]
    if not re.fullmatch(IDENT, n):
        die("bad identifier %r" % n)
    return n.replace(".", "_")

class Ctx:
    def __init__(self):
        self.ctor = {"True": "true", "False": "false"}   # Bend ctor -> Lean term head
        self.arity = {"True": 0, "False": 0}

def tokenize(s):
    toks, i = [], 0
    while i < len(s):
        c = s[i]
        if c == " ":
            i += 1; continue
        m = re.match(r"\d+n", s[i:])
        if m:
            toks.append(m.group(0)); i += len(m.group(0)); continue
        m = re.match(IDENT, s[i:])
        if m:
            toks.append(m.group(0)); i += len(m.group(0)); continue
        if c in "{}(),+_":
            toks.append(c); i += 1; continue
        die("unexpected character %r in %r" % (c, s))
    return toks

def ty(s):
    s = s.strip()
    if "&" in s:
        a, b = s.split("&", 1)
        return "(%s × %s)" % (ty(a), ty(b))
    if s in ("Nat", "Bool", "Type") or re.fullmatch(r"(K\.)?[A-Z][A-Za-z0-9_]*", s):
        return lname(s)
    die("unsupported type %r" % s)

class Expr:
    def __init__(self, toks, cx):
        self.t, self.i, self.cx = toks, 0, cx
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def take(self, want=None):
        tok = self.peek()
        if tok is None or (want is not None and tok != want):
            die("expected %r, found %r in %r" % (want, tok, " ".join(self.t)))
        self.i += 1
        return tok
    def args(self, close):
        out = []
        if self.peek() == close:
            self.take(close); return out
        while True:
            out.append(self.expr())
            if self.peek() == ",":
                self.take(",")
            else:
                self.take(close); return out
    def expr(self):
        tok = self.take()
        if re.fullmatch(r"\d+n", tok):
            k = int(tok[:-1])
            if self.peek() == "+":
                self.take("+"); return "(%s + %d)" % (self.expr(), k)
            return str(k)
        if tok == "(":
            a = self.expr(); self.take(","); b = self.expr(); self.take(")")
            return "(%s, %s)" % (a, b)
        if re.fullmatch(IDENT, tok):
            if self.peek() == "{":
                self.take("{"); a = self.args("}")
                c = tok[2:] if tok.startswith("K.") else tok
                if c not in self.cx.ctor: die("unknown constructor %r" % tok)
                if len(a) != self.cx.arity[c]: die("arity mismatch for %r" % tok)
                return self.cx.ctor[c] if not a else "(%s %s)" % (self.cx.ctor[c], " ".join(a))
            if self.peek() == "(":
                self.take("("); a = self.args(")")
                return lname(tok) if not a else "(%s %s)" % (lname(tok), " ".join(a))
            if "." in tok: die("dotted name used as a variable: %r" % tok)
            return tok
        die("unexpected token %r" % tok)

def expr(s, cx):
    e = Expr(tokenize(s), cx)
    r = e.expr()
    if e.peek() is not None: die("trailing tokens in expression %r" % s)
    return r

def split_top(s):
    parts, depth, cur = [], 0, ""
    for c in s:
        if c == "{": depth += 1
        if c == "}": depth -= 1
        if c == " " and depth == 0:
            if cur: parts.append(cur)
            cur = ""
        else:
            cur += c
    if cur: parts.append(cur)
    return parts

def pat(p, cx):
    if p == "_": return "_"
    m = re.fullmatch(r"(\d+)n", p)
    if m: return m.group(1)
    m = re.fullmatch(r"(\d+)n\+([a-z_][A-Za-z0-9_]*)", p)
    if m: return "%s + %s" % (m.group(2), m.group(1))
    m = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\{(.*)\}", p)
    if m:
        c = m.group(1)
        if c not in cx.ctor: die("unknown constructor in pattern %r" % p)
        bs = [b.strip().lstrip("+-") for b in m.group(2).split(",")] if m.group(2).strip() else []
        if len(bs) != cx.arity[c]: die("pattern arity mismatch %r" % p)
        for b in bs:
            if not re.fullmatch(r"[a-z_][A-Za-z0-9_]*", b): die("bad binder %r" % b)
        return cx.ctor[c] if not bs else "%s %s" % (cx.ctor[c], " ".join(bs))
    if re.fullmatch(r"[a-z_][A-Za-z0-9_]*", p): return p
    die("unsupported pattern %r" % p)

def block(lines, ind, cx, out_ind):
    """lines: list of (indent, text) all with indent >= ind; returns Lean text lines"""
    pad = " " * out_ind
    if not lines: die("empty block")
    i0, t0 = lines[0]
    if i0 != ind: die("bad indentation at %r" % t0)
    m = re.fullmatch(r"match ([a-z_][A-Za-z0-9_]*(?: [a-z_][A-Za-z0-9_]*)*):", t0)
    if m:
        scr = m.group(1).split(" ")
        res = [pad + "match %s with" % ", ".join(scr)]
        k = 1
        if k >= len(lines): die("match without cases")
        while k < len(lines):
            ci, ct = lines[k]
            mc = re.fullmatch(r"case (.*):", ct)
            if ci != ind + 2 or not mc: die("expected case at indent %d, found %r" % (ind + 2, ct))
            ps = split_top(mc.group(1))
            if len(ps) != len(scr): die("case arity %r" % ct)
            j = k + 1
            while j < len(lines) and lines[j][0] > ind + 2: j += 1
            res.append(pad + "| %s =>" % ", ".join(pat(p, cx) for p in ps))
            res += block(lines[k + 1:j], ind + 4, cx, out_ind + 4)
            k = j
        return res
    m = re.fullmatch(r"\(([a-z_]\w*), ([a-z_]\w*)\) = (.*)", t0)
    if m:
        return [pad + "let (%s, %s) := %s" % (m.group(1), m.group(2), expr(m.group(3), cx))] + block(lines[1:], ind, cx, out_ind)
    if len(lines) != 1: die("extra lines after expression %r" % t0)
    return [pad + expr(t0, cx)]

def items(src):
    """top-level items: (header, [(indent, text)...]); full-line '#' comments and blanks skipped"""
    out, cur = [], None
    for raw in src.split("\n"):
        if not raw.strip() or raw.lstrip().startswith("#"): continue
        if "\t" in raw or "#" in raw: die("tab or inline comment: %r" % raw)
        ind = len(raw) - len(raw.lstrip(" ")); t = raw.strip()
        if ind == 0:
            cur = (t, []); out.append(cur)
        else:
            if cur is None: die("indented line before any item")
            cur[1].append((ind, t))
    return out

def emit_type(name, body, cx, out):
    if name in ("Bool", "Nat"): die("Bool/Nat are identified with Lean's, not translated")
    out.append("inductive %s where" % lname(name))
    for ind, t in body:
        m = re.fullmatch(r"([A-Z][A-Za-z0-9_]*)\{(.*)\}", t)
        if ind != 2 or not m: die("bad constructor line %r" % t)
        c, fs = m.group(1), m.group(2).strip()
        fields = []
        if fs:
            for f in fs.split(","):
                mf = re.fullmatch(r"\s*([a-z_]\w*): (.+?)\s*", f)
                if not mf: die("bad field %r" % f)
                fields.append("(%s : %s)" % (mf.group(1), ty(mf.group(2))))
        if c in cx.ctor: die("duplicate constructor %r" % c)
        cx.ctor[c] = "%s.%s" % (lname(name), c); cx.arity[c] = len(fields)
        out.append("  | %s %s" % (c, " ".join(fields)) if fields else "  | %s" % c)
    out.append("")

def emit_def(hdr, body, cx, out):
    m = re.fullmatch(r"def (%s)\((.*)\) -> (.+):" % IDENT, hdr)
    if not m: die("bad def header %r" % hdr)
    name, ps, ret = m.group(1), m.group(2), m.group(3)
    params = []
    if ps.strip():
        for p in ps.split(","):
            mp = re.fullmatch(r"\s*[+-]?([a-zA-Z_]\w*): (.+?)\s*", p)
            if not mp: die("bad parameter %r" % p)
            params.append("(%s : %s)" % (mp.group(1), ty(mp.group(2))))
    out.append("def %s%s : %s :=" % (lname(name), "".join(" " + p for p in params), ty(ret)))
    out += block(body, 2, cx, 2)
    out.append("")

def main():
    a = sys.argv[1:]
    cx = Ctx()
    if a and a[0] == "kernel" and len(a) == 4:
        base, kern, outp = a[1], a[2], a[3]
        bsrc, ksrc = open(base).read(), open(kern).read()
        out = ["/-! GENERATED by bendlink/bend2lean.py -- do not edit.",
               "  base   : %s sha256 %s (whitelist: %s)" % (base.split("/")[-1], hashlib.sha256(bsrc.encode()).hexdigest(), ", ".join(BASE_WHITELIST)),
               "  kernel : %s sha256 %s -/" % (kern.split("/")[-1], hashlib.sha256(ksrc.encode()).hexdigest()),
               "set_option linter.unusedVariables false", "namespace BK", ""]
        bitems = {}
        for hdr, body in items(bsrc):
            m = re.match(r"(?:def|type) (%s)" % IDENT, hdr)
            if m and m.group(1) in BASE_WHITELIST:
                if m.group(1) in bitems: die("duplicate base item %s" % m.group(1))
                bitems[m.group(1)] = (hdr, body)
        for w in BASE_WHITELIST:
            if w not in bitems: die("base item %s not found" % w)
            hdr, body = bitems[w]
            mt = re.fullmatch(r"type (%s) is Data:" % IDENT, hdr)
            emit_type(mt.group(1), body, cx, out) if mt else emit_def(hdr, body, cx, out)
        kit = items(ksrc)
        if not kit or kit[0][0] != "import Base" or kit[0][1]: die("kernel must start with exactly `import Base`")
        for hdr, body in kit[1:]:
            mt = re.fullmatch(r"type (%s) is Data:" % IDENT, hdr)
            if mt: emit_type(mt.group(1), body, cx, out)
            elif hdr.startswith("def "): emit_def(hdr, body, cx, out)
            else: die("unsupported top-level item %r" % hdr)
        out.append("end BK")
    elif a and a[0] == "progs" and len(a) >= 3:
        outp = a[1]
        # constructor table of the kernel types the prog terms may use
        for t, cs in {"Op": ["LdA", "LdB", "Mul", "Acc", "Wrap", "StT", "LdT", "Sub", "Abs", "Sq", "Pos", "Bit", "AbsT", "Ne0"], "Stmt": [("Alloc", 0), ("Loop", 1)],
                      "Ops": [("ONil", 0), ("OCons", 2)], "Stmts": [("PNil", 0), ("PCons", 2)]}.items():
            for c in cs:
                c, n = (c, 0) if isinstance(c, str) else c
                cx.ctor[c] = "BK.%s.%s" % (t, c); cx.arity[c] = n
        out = ["import Bridge.BendKernel", "/-! GENERATED by bendlink/bend2lean.py -- do not edit. -/", ""]
        for spec in a[2:]:
            nm, path = spec.split("=", 1)
            src = open(path).read()
            it = items(src)
            if [h for h, _ in it[:2]] != ["import Base", "import ./kernel.bend as K"] or it[0][1] or it[1][1]:
                die("%s: preamble is not exactly `import Base` / `import ./kernel.bend as K`" % path)
            if len(it) != 3 or it[2][0] != "def prog() -> K.Stmts:" or len(it[2][1]) != 1 or it[2][1][0][0] != 2:
                die("%s: expected exactly one `def prog() -> K.Stmts:` with a one-line body" % path)
            out += ["-- %s sha256 %s" % (path, hashlib.sha256(src.encode()).hexdigest()),
                    "def BK.P_%s.prog : BK.Stmts :=" % nm, "  " + expr(it[2][1][0][1], cx), ""]
    else:
        print(__doc__); sys.exit(64)
    open(outp, "w").write("\n".join(out) + "\n")

try:
    main()
except Unsupported as e:
    print("bend2lean: UNSUPPORTED:", e); sys.exit(2)
