#!/usr/bin/env bash
# Controls made by hand-mutating the CONCRETE emitted positive file (not via gen.py).
set -e; cd "$(dirname "$0")"; P=../variants/pos/i8dot.c
FOR='^  for (size_t i = 0; i < n; i++) {$'
# buffers (same sum)
sed "s|$FOR|  int32_t t[n ? n : 1];\n&|; s|^    acc = acc + r0;$|    t[i] = r0;\n    acc = acc + t[i];|" $P > stack_vla.c
sed "s|$FOR|  static int32_t t[131071];\n&|; s|^    acc = acc + r0;$|    t[i] = r0;\n    acc = acc + t[i];|" $P > static_arr.c
# no buffer, but outside the grammar
sed 's|^    acc = acc + r0;$|&\n    acc = mystery(acc);|' $P > unknown_call.c
sed 's|^    r0 = r0 \* r1;$|&\n    r1 = (int32_t)a[i];|' $P > double_load.c
# order/scope controls: every line is a known statement, but misplaced
sed "/^  \*out = acc;$/d; s|$FOR|  *out = acc;\n&|" $P > early_store.c        # reviewer's case: single output store moved before the loop
sed "s|$FOR|  *out = acc;\n  return 0;\n&|" $P > early_return.c             # premature output + return before the loop
sed '/^  if (n > I8DOT_MAX_N) return -1;$/d' $P > missing_guard.c
sed '0,/^  }$/s//  }\n  acc = acc + r0;/' $P > trailing_stmt.c                 # extra Acc after the loop
# lexical: a line splice turns the output store into part of a // comment
sed 's|^  \*out = acc;$|  // store result \\\n  *out = acc;|' $P > comment_splice.c
