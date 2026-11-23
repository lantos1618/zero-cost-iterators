#!/usr/bin/env bash
# i8red milestone replay: three scalar signed-INT8 reductions (dot, L1, squared L2) under one gate.
# Raw outputs + exit codes -> results_i8red/*.txt; summary -> EVIDENCE_i8red.txt (via tee).
# Needs: bend 2.0.40 (~/.bend/bin/bend), elan + leanprover/lean4:v4.15.0, gcc, clang, python3.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}
UNEXPECTED=0; TOTAL=0
R=$PWD/results_i8red; rm -rf "$R"; mkdir -p "$R"
sec() { printf '\n==================== %s\n' "$1"; }
run() { local n=$1 d=$2 want=$3; shift 3; (cd "$d" && "$@") > "$R/$n.txt" 2>&1; local s=$?
  echo "exit=$s" >> "$R/$n.txt"; TOTAL=$((TOTAL+1)); local tag=ok; [ "$s" = "$want" ] || { tag=UNEXPECTED; UNEXPECTED=$((UNEXPECTED+1)); }
  printf '%-34s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -m1 -E 'REJECT:|VERDICT|PROOFS|fails=|error|differ' "$R/$n.txt")"; }
C=$PWD/bridge/.lake/build/bin/i8check

sec "versions"
$BEND version; (cd bridge && lean --version); gcc --version | head -1; clang --version | head -1; python3 --version; uname -sm

sec "emit with gen.py (trusted) and compare with the committed emitted files"
T=$(mktemp -d)
for v in pos wrap buf l1 l2; do ./gen.py ir/$v.json $T/$v; done
for v in l2_badguard l2_buf; do ./gen.py ir/$v.json $T/$v; done
./gen.py ir/l1_noabs.json $T/l1_noabs
for v in pos wrap buf l1 l2; do run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c variants/$v/i8dot.c && cmp $T/$v/prog.bend variants/$v/prog.bend"; done
for v in l2_badguard l2_buf; do run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c red/$v/i8dot.c && cmp $T/$v/prog.bend red/$v/prog.bend"; done
run emit_l1_noabs_same . 0 sh -c "cmp $T/l1_noabs/i8dot.c controls/l1_noabs/i8dot.c && cmp $T/l1_noabs/prog.bend controls/l1_noabs/prog.bend"
run pos_C_byteidentical_to_r5 . 0 cmp variants/pos/i8dot.c $HOME/i8dot-bend-r5/variants/pos/i8dot.c
for v in pos wrap buf l1 l2; do run kernel_copy_${v} . 0 cmp kernel.bend variants/$v/kernel.bend; done
sha256sum kernel.bend variants/*/prog.bend variants/*/i8dot.c red/*/i8dot.c controls/*/i8dot.c

sec "Bend --verdict (actual kernel.bend + actual prog.bend)"
run bend_pos_PROOF variants/pos 0 $BEND PROOF.bend --verdict
run bend_l1_PROOF_RED variants/l1 0 $BEND PROOF_RED.bend --verdict
run bend_l2_PROOF_RED variants/l2 0 $BEND PROOF_RED.bend --verdict

sec "trusted Bend->Lean translation: regenerate and require byte-identical Lean"
(cd bendlink && ./bend2lean.py kernel base.bend.pinned ../kernel.bend $T/BendKernel.lean && ./bend2lean.py progs $T/BendProgs.lean pos=../variants/pos/prog.bend wrap=../variants/wrap/prog.bend buf=../variants/buf/prog.bend l1=../variants/l1/prog.bend l2=../variants/l2/prog.bend)
run base_pinned_same . 0 cmp bendlink/base.bend.pinned $HOME/.bend/bend2/base.bend
run translate_kernel_same . 0 cmp $T/BendKernel.lean bridge/Bridge/BendKernel.lean
run translate_progs_same . 0 cmp $T/BendProgs.lean bridge/Bridge/BendProgs.lean

sec "Lean build (checker + all proofs) and axiom audit"
run lean_build bridge 0 lake build
run lean_audit bridge 0 lake env lean Audit.lean
echo "audited theorems: $(grep -c '^#print' bridge/Audit.lean)"; grep -oE "\[[^]]*\]|does not depend on any axioms" $R/lean_audit.txt | sort | uniq -c
run no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" bridge/Bridge

sec "public gate on the actual emitted files (0 PASS, 2 C REJECT, 3 IR MISMATCH, 4 Bend REJECT, 5 UNCERTIFIED)"
for v in pos l1 l2; do run gate_exact_$v . 0 $C exact variants/$v/i8dot.c variants/$v/prog.bend; run gate_match_$v . 0 $C match variants/$v/i8dot.c variants/$v/prog.bend; done
run gate_exact_wrap_own . 3 $C exact variants/wrap/i8dot.c variants/wrap/prog.bend
run gate_match_wrap_own . 0 $C match variants/wrap/i8dot.c variants/wrap/prog.bend
run ctl_buf_dot_r5 . 2 $C exact variants/buf/i8dot.c variants/buf/prog.bend
run ctl_buf_l2_diffbuffer . 2 $C exact red/l2_buf/i8dot.c red/l2_buf/prog.bend
run ctl_l2_wrong_guard_131071 . 2 $C exact red/l2_badguard/i8dot.c variants/l2/prog.bend
run ctl_l2_wrong_guard_match . 2 $C match red/l2_badguard/i8dot.c red/l2_badguard/prog.bend
run ctl_l2_missing_guard . 2 $C exact controls/l2_noguard/i8dot.c variants/l2/prog.bend
run ctl_l1_arith_signflip . 2 $C exact controls/l1_signflip/i8dot.c variants/l1/prog.bend
run ctl_l1_noabs_exact_own . 3 $C exact controls/l1_noabs/i8dot.c controls/l1_noabs/prog.bend
run ctl_l1_noabs_match_own . 5 $C match controls/l1_noabs/i8dot.c controls/l1_noabs/prog.bend
run ctl_l1_noabs_vs_l1prog . 3 $C exact controls/l1_noabs/i8dot.c variants/l1/prog.bend
run ctl_l1C_vs_l2prog . 3 $C exact variants/l1/i8dot.c variants/l2/prog.bend
run ctl_l2C_vs_l1prog . 3 $C exact variants/l2/i8dot.c variants/l1/prog.bend
run ctl_dotC_vs_l2prog . 3 $C exact variants/pos/i8dot.c variants/l2/prog.bend
sed 's/^def prog()/def prog2()/' variants/l2/prog.bend > $T/tamper.bend
run ctl_l2prog_tampered . 4 $C exact variants/l2/i8dot.c $T/tamper.bend
run ctl_r5_overflow_match . 5 $C match checker_tests/overflow/i8dot.c checker_tests/overflow/prog.bend

sec "negative control: meaningful change to zsub in kernel.bend (a - b -> a + b)"
N=$T/neg; mkdir -p $N; sed 's/Z{Nat.add(p, m), Nat.add(n, q)}/Z{Nat.add(p, q), Nat.add(n, m)}/' kernel.bend > $N/kernel_zsubmut.bend
run negB_kernel_changed . 1 cmp -s kernel.bend $N/kernel_zsubmut.bend
mkdir -p $N/l1; cp variants/l1/prog.bend variants/l1/PROOF_RED.bend $N/l1/; cp $N/kernel_zsubmut.bend $N/l1/kernel.bend
run negB_bend_l1_PROOF_RED_still_passes $N/l1 0 $BEND PROOF_RED.bend --verdict
(cd bendlink && ./bend2lean.py kernel base.bend.pinned $N/kernel_zsubmut.bend $N/BendKernel.lean) > /dev/null
run negB_lean_differs . 1 cmp -s $N/BendKernel.lean bridge/Bridge/BendKernel.lean
cp -a bridge $N/bridge; cp $N/BendKernel.lean $N/bridge/Bridge/BendKernel.lean
run negB_link_build_fails $N/bridge 1 lake build Bridge.BendLink

sec "finite native differential tests (not proof): n=0, extremes, around each guard, deterministic random"
for v in pos:0:131071 l1:1:8421504 l2:2:33025; do IFS=: read n k Nn <<< "$v"
  for cc in "gcc -O2" "gcc -O3 -march=native" "clang -O3" "gcc -O1 -fsanitize=undefined -fno-sanitize-recover=all" "clang -O1 -fsanitize=undefined -fno-sanitize-recover=all"; do
    tag=$(echo "$cc" | tr -c 'a-zA-Z0-9\n' '_')
    run native_${n}_$tag native 0 sh -c "$cc -std=c11 -o t_$n test.c ../variants/$n/i8dot.c && ./t_$n $k $Nn"; done; done
for o in pos l1 l2; do gcc -O2 -c -o $T/$o.o variants/$o/i8dot.c; echo "$o undefined symbols: [$(nm -u $T/$o.o | tr '\n' ' ')]"; done

sec "summary"
echo "TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
rm -rf "$T"
[ $UNEXPECTED = 0 ]
