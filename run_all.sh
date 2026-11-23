#!/usr/bin/env bash
# Reproduces every result. Raw outputs + exit codes go to results/*.txt; the console log is EVIDENCE.txt.
# Needs: bend 2.0.40 (~/.bend/bin/bend), elan with leanprover/lean4:v4.15.0, gcc, clang, python3, objdump.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}   # override: BEND=/path/to/bend ./run_all.sh
UNEXPECTED=0; TOTAL=0
# note: the -O2 objdump counts below are code-shape observations for x86-64 only
R=$PWD/results; rm -rf "$R"; mkdir -p "$R"
sec() { printf '\n==================== %s\n' "$1"; }
# run NAME DIR CMD...: raw output to results/NAME.txt, exit code appended, summary line printed
# run NAME DIR EXPECTED_EXIT CMD...: raw output to results/NAME.txt with exit code; a different exit code is a failed replay
run() { local n=$1 d=$2 want=$3; shift 3; (cd "$d" && "$@") > "$R/$n.txt" 2>&1; local s=$?
  echo "exit=$s" >> "$R/$n.txt"; TOTAL=$((TOTAL+1)); local tag=ok; [ "$s" = "$want" ] || { tag=UNEXPECTED; UNEXPECTED=$((UNEXPECTED+1)); }
  printf '%-34s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -m1 -E 'PROOFS|VERDICT|mismatches|error|Error' "$R/$n.txt")"; }

sec "versions"
$BEND version; sha256sum $BEND; ls ~/.bend/bendtt/*/bendtt; (cd lean && lean --version); gcc --version | head -1; clang --version | head -1; python3 --version; uname -sm

sec "emit (gen.py, trusted) and copy the shared Bend files"
for v in pos wrap buf; do ./gen.py ir/$v.json variants/$v; cp kernel.bend LAWS.bend PROOF.bend variants/$v/; done
# r4 control: an IR outside the certified set, emitted by the shipped gen.py (never compiled/run natively: it overflows int32)
echo '{"name": "overflow", "prog": [{"loop": ["LdA", "LdB", "Mul", "Mul", "Mul", "Mul", "Acc"]}]}' > ir/overflow.json
mkdir -p checker_tests/overflow && ./gen.py ir/overflow.json checker_tests/overflow
cp variants/pos/prog.bend prog.bend
sha256sum kernel.bend variants/*/kernel.bend LAWS.bend variants/*/LAWS.bend PROOF.bend variants/*/PROOF.bend prog.bend variants/*/prog.bend variants/*/i8dot.c

sec "Bend: LAWS.bend + PROOF.bend per variant (same LAWS/PROOF bytes; only prog.bend differs)"
for v in pos wrap buf; do
  want=1; [ $v = pos ] && want=0
  run bend_${v}_PROOF          variants/$v $want $BEND PROOF.bend
  run bend_${v}_PROOF_verdict  variants/$v $want $BEND PROOF.bend --verdict
done
run bend_root_PROOF_verdict . 0 $BEND PROOF.bend --verdict
sec "Bend: mutant-specific checked facts"
run bend_wrap_REFUTE             variants/wrap 0 $BEND REFUTE.bend
run bend_wrap_REFUTE_verdict     variants/wrap 0 $BEND REFUTE.bend --verdict
run bend_wrap_NOBUF_WRAP         variants/wrap 0 $BEND NOBUF_WRAP.bend
run bend_wrap_NOBUF_WRAP_verdict variants/wrap 0 $BEND NOBUF_WRAP.bend --verdict
run bend_buf_REFUTE              variants/buf 0 $BEND REFUTE.bend
run bend_buf_REFUTE_verdict      variants/buf 0 $BEND REFUTE.bend --verdict
run bend_demo_run                . 0 $BEND demo.bend
for f in "$R"/bend_*.txt; do echo "--- $(basename $f)"; head -14 "$f"; done

sec "C validator (check_c.py, independent of gen.py) on the exact emitted files and on hand-mutated emitted output"
# nobuf gate: 0 PASS / 1 BUFFER / 2 REJECT;  exact gate vs ir/pos.json (the IR whose PROOF.bend passed): 0 / 2 REJECT / 3 MISMATCH
for v in pos wrap; do run check_match_$v . 0 ./check_c.py --gate match variants/$v/i8dot.c ir/$v.json; done
./checker_tests/make.sh
for spec in pos:0:0 wrap:0:3 buf:1:2; do IFS=: read v nb ex <<< "$spec"
  run check_nobuf_$v . $nb ./check_c.py --gate nobuf variants/$v/i8dot.c
  run check_exact_$v . $ex ./check_c.py --gate exact variants/$v/i8dot.c ir/pos.json; done
for spec in stack_vla:1 static_arr:1 unknown_call:2 double_load:2 early_store:2 early_return:2 missing_guard:2 trailing_stmt:2 comment_splice:2; do IFS=: read c nb <<< "$spec"
  run check_nobuf_ctl_$c . $nb ./check_c.py --gate nobuf checker_tests/$c.c
  run check_exact_ctl_$c . 2 ./check_c.py --gate exact checker_tests/$c.c ir/pos.json; done
for f in "$R"/check_*.txt; do echo "--- $(basename $f)"; cat "$f"; done
echo "--- r2 Python baseline on the r4 overflow control (unproved; it has no totality notion and accepts it):"
run check_match_ctl_overflow . 0 ./check_c.py --gate match checker_tests/overflow/i8dot.c ir/overflow.json; cat "$R/check_match_ctl_overflow.txt"
sec "the r1 validator (statement-wise, no order/scope) accepted the early-store control; kept for the record"
python3 checker_tests/check_c_r1.py checker_tests/early_store.c ir/pos.json | tail -2

sec "Lean: int32 prefix-sum safety contract"
run lean_safety lean 0 lean Safety.lean; cat "$R/lean_safety.txt"

sec "native finite executions (emitted i8dot.c vs independent ref.c)"
for v in pos wrap buf; do for CC in gcc clang; do for O in -O0 -O2; do
  $CC $O -std=c11 -Wall -Wextra -o /tmp/i8_$v native/test.c native/ref.c variants/$v/i8dot.c
  want=0; [ $v = wrap ] && want=1
  run native_${v}_${CC}${O} . $want /tmp/i8_$v
done; done; done
# UBSan and ASan as separate builds; ASan run under setarch -R (see README)
clang -O1 -g -std=c11 -fsanitize=undefined -fno-sanitize-recover=all -o /tmp/i8_ub native/test.c native/ref.c variants/pos/i8dot.c
run native_pos_clang_ubsan . 0 /tmp/i8_ub
clang -O1 -g -std=c11 -fsanitize=address -o /tmp/i8_as native/test.c native/ref.c variants/pos/i8dot.c
run native_pos_clang_asan . 0 setarch -R /tmp/i8_as   # ASLR off: clang-14 ASan segfaulted intermittently at startup with ASLR (3/6 plain runs, 0/6 with setarch -R)
for f in native_pos_gcc-O2 native_wrap_gcc-O2 native_buf_gcc-O2 native_pos_clang_ubsan native_pos_clang_asan; do echo "--- $f"; cat "$R/$f.txt"; done

sec "native: order/lexical controls compiled as-is (expected to mismatch the reference)"
for c in early_store early_return comment_splice; do gcc -O2 -std=c11 -o /tmp/i8_$c native/test.c native/ref.c checker_tests/$c.c 2>/dev/null
  run native_ctl_${c}_gcc-O2 . 1 /tmp/i8_$c; grep -E "mixed_signs|wrap_witness" "$R/native_ctl_${c}_gcc-O2.txt"; done

sec "optimizer/code-shape evidence for the positive kernel (-O2; not a theorem)"
for CC in gcc clang; do
  $CC -O2 -std=c11 -c -o /tmp/pos.o variants/pos/i8dot.c; objdump -d --no-show-raw-insn /tmp/pos.o > "$R/objdump_pos_$CC-O2.txt"
  echo "[$CC -O2] insns=$(grep -cE '^\s+[0-9a-f]+:' "$R/objdump_pos_$CC-O2.txt") calls=$(grep -cE '\scall' "$R/objdump_pos_$CC-O2.txt") stack_stores=$(grep -cE 'mov[a-z]*\s+[^,]+,.*\((%rsp|%rbp)\)' "$R/objdump_pos_$CC-O2.txt") simd_xmm=$(grep -c xmm "$R/objdump_pos_$CC-O2.txt")"
done
for CC in gcc clang; do $CC -O2 -std=c11 -c -o /tmp/buf.o variants/buf/i8dot.c; echo "[$CC -O2 buf] external calls (relocations): $(objdump -dr /tmp/buf.o | grep -oE 'R_X86_64_PLT32\s+\w+' | awk '{print $2}' | sort | uniq -c | tr -s ' \n' ' ')"; done
for CC in gcc clang; do $CC -O2 -std=c11 -c -o /tmp/pos.o variants/pos/i8dot.c; echo "[$CC -O2 pos] external calls (relocations): $(objdump -dr /tmp/pos.o | grep -cE 'R_X86_64_PLT32')"; done

sec "r3: Lean bridge (authoritative checker i8check + bridge theorems), Lean v4.15.0, core only"
run lean_bridge_build bridge 0 lake build
run lean_bridge_audit bridge 0 lake env lean Audit.lean
cat "$R/lean_bridge_audit.txt"
echo "--- scan (code tokens, comments excluded by word match):"
grep -nwE "sorry|admit|native_decide|axiom|extern|unsafe|partial|opaque|implemented_by" bridge/Bridge/*.lean bridge/Main.lean | grep -v -- "--\|/-\|admitted" || echo "scan: none"
I8=bridge/.lake/build/bin/i8check
sed 's|^def prog() -> K.Stmts:$|def prog2() -> K.Stmts:|' variants/pos/prog.bend > checker_tests/prog_renamed.bend
{ cat variants/pos/prog.bend; echo 'def extra() -> K.Stmts:'; } > checker_tests/prog_extra.bend
# gate  file  prog.bend  expected-exit     (0 PASS, 2 C REJECT, 3 IR MISMATCH, 4 prog.bend REJECT, 5 UNCERTIFIED)
while read g c b w; do n="i8check_${g}_$(basename $(dirname $c))_$(basename $c .c)_vs_$(basename $(dirname $b))$(basename $b .bend | sed 's/^prog//')"
  run "$n" . "$w" $I8 "$g" "$c" "$b"; done <<'EOT'
exact variants/pos/i8dot.c variants/pos/prog.bend 0
match variants/pos/i8dot.c variants/pos/prog.bend 0
exact variants/wrap/i8dot.c variants/pos/prog.bend 3
match variants/wrap/i8dot.c variants/wrap/prog.bend 0
exact variants/wrap/i8dot.c variants/wrap/prog.bend 3
exact variants/buf/i8dot.c variants/pos/prog.bend 2
match variants/buf/i8dot.c variants/buf/prog.bend 2
exact checker_tests/early_store.c variants/pos/prog.bend 2
match checker_tests/early_store.c variants/pos/prog.bend 2
exact checker_tests/early_return.c variants/pos/prog.bend 2
match checker_tests/early_return.c variants/pos/prog.bend 2
exact checker_tests/comment_splice.c variants/pos/prog.bend 2
exact checker_tests/missing_guard.c variants/pos/prog.bend 2
exact checker_tests/trailing_stmt.c variants/pos/prog.bend 2
exact checker_tests/unknown_call.c variants/pos/prog.bend 2
exact checker_tests/double_load.c variants/pos/prog.bend 2
exact checker_tests/stack_vla.c variants/pos/prog.bend 2
exact checker_tests/static_arr.c variants/pos/prog.bend 2
match checker_tests/overflow/i8dot.c checker_tests/overflow/prog.bend 5
exact checker_tests/overflow/i8dot.c checker_tests/overflow/prog.bend 3
match checker_tests/overflow/i8dot.c variants/pos/prog.bend 3
exact variants/pos/i8dot.c checker_tests/prog_renamed.bend 4
exact variants/pos/i8dot.c checker_tests/prog_extra.bend 4
EOT
for f in "$R"/i8check_*.txt; do echo "--- $(basename $f)"; cat "$f"; done
sec "r3: Lean C-subset semantics (C.cRun) executed on parsed files, small witnesses (finite, not a theorem)"
for c in variants/pos/i8dot.c variants/wrap/i8dot.c checker_tests/overflow/i8dot.c checker_tests/early_store.c checker_tests/early_return.c checker_tests/trailing_stmt.c; do
  run "csem_$(basename $(dirname $c))_$(basename $c .c)" . 0 $I8 csem $c; cat "$R/csem_$(basename $(dirname $c))_$(basename $c .c).txt"; done

sec "r5: Bend -> Lean translation link (bendlink/bend2lean.py, trusted) and all-input link theorems (Bridge/BendLink.lean)"
BASE_INST=$HOME/.bend/bend2/base.bend
echo "installed base (opened by bend 2.0.40, see README): $(sha256sum $BASE_INST)"
echo "pinned copy                                       : $(sha256sum bendlink/base.bend.pinned)"
run r5_base_pin . 0 cmp $BASE_INST bendlink/base.bend.pinned
T=$R/r5_regen; mkdir -p $T
run r5_translate_kernel . 0 bendlink/bend2lean.py kernel bendlink/base.bend.pinned kernel.bend $T/BendKernel.lean
run r5_translate_progs . 0 bendlink/bend2lean.py progs $T/BendProgs.lean pos=variants/pos/prog.bend wrap=variants/wrap/prog.bend buf=variants/buf/prog.bend
# the generated files record relative source paths: regenerate from the same relative paths used for the committed copies
(cd bendlink && ./bend2lean.py kernel base.bend.pinned ../kernel.bend $T/BendKernel.lean && ./bend2lean.py progs $T/BendProgs.lean pos=../variants/pos/prog.bend wrap=../variants/wrap/prog.bend buf=../variants/buf/prog.bend)
run r5_regen_eq_committed_kernel . 0 cmp $T/BendKernel.lean bridge/Bridge/BendKernel.lean
run r5_regen_eq_committed_progs . 0 cmp $T/BendProgs.lean bridge/Bridge/BendProgs.lean
run r5_lake_build bridge 0 lake build
run r5_audit bridge 0 lake env lean Audit.lean
cat "$R/r5_audit.txt"
echo "--- negative control A: deliberate evaluator change in kernel.bend (w8.nat: Nat.is_lt(r, 128n) -> 127n)"
diff kernel.bend bendlink/neg/kernel_w8mut.bend
N=$R/r5_neg; rm -rf $N; mkdir -p $N/pos $N/wrap
for v in pos wrap; do cp variants/$v/*.bend $N/$v/; cp bendlink/neg/kernel_w8mut.bend $N/$v/kernel.bend; done
run r5_negA_bend_pos_PROOF_verdict $N/pos 0 $BEND PROOF.bend --verdict
run r5_negA_bend_wrap_REFUTE_verdict $N/wrap 0 $BEND REFUTE.bend --verdict
run r5_negA_bend_wrap_NOBUF_verdict $N/wrap 0 $BEND NOBUF_WRAP.bend --verdict
(cd bendlink && ./bend2lean.py kernel base.bend.pinned neg/kernel_w8mut.bend $N/BendKernel.lean) > /dev/null
run r5_negA_regen_differs . 1 cmp $N/BendKernel.lean bridge/Bridge/BendKernel.lean
mkdir -p $N/bridge && cp -r bridge/lakefile.lean bridge/lean-toolchain bridge/Bridge.lean bridge/Bridge bridge/Main.lean $N/bridge/
cp $N/BendKernel.lean $N/bridge/Bridge/BendKernel.lean
run r5_negA_lean_link_build $N/bridge 1 lake build Bridge.BendLink
grep -m3 -E "error" "$R/r5_negA_lean_link_build.txt"
rm -rf $N/bridge/.lake
echo "--- negative control B: unsupported syntax is refused by the translator (fail-closed)"
run r5_negB_translator_rejects bendlink 2 ./bend2lean.py kernel base.bend.pinned neg/kernel_unsupported.bend /dev/null
cat "$R/r5_negB_translator_rejects.txt"

sec "replay summary"
echo "expected exit codes: $((TOTAL-UNEXPECTED))/$TOTAL"
[ "$UNEXPECTED" = 0 ] && echo "REPLAY OK" || { echo "REPLAY FAILED ($UNEXPECTED unexpected)"; exit 1; }
