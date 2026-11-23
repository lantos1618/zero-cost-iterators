#!/usr/bin/env bash
# i8red5 replay: five scalar signed-INT8 reductions (dot, L1, squared L2, Hamming, one-sided L1) under one gate
# and one shared Lean induction. Raw outputs + exit codes -> results_i8red5/*.txt; summary on stdout (tee it).
# Needs: bend 2.0.40 (~/.bend/bin/bend), elan + leanprover/lean4:v4.15.0, gcc, clang, python3, ~5 GiB free RAM.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}
UNEXPECTED=0; TOTAL=0
R=$PWD/results_i8red5; rm -rf "$R"; mkdir -p "$R"
sec() { printf '\n==================== %s\n' "$1"; }
run() { local n=$1 d=$2 want=$3; shift 3; (cd "$d" && "$@") > "$R/$n.txt" 2>&1; local s=$?
  echo "exit=$s" >> "$R/$n.txt"; TOTAL=$((TOTAL+1)); local tag=ok; [ "$s" = "$want" ] || { tag=UNEXPECTED; UNEXPECTED=$((UNEXPECTED+1)); }
  printf '%-40s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -m1 -E 'REJECT:|VERDICT|PROOFS|fails=|error|differ' "$R/$n.txt" | cut -c1-110)"; }
C=$PWD/bridge/.lake/build/bin/i8check
POS="pos l1 l2 ham osl"

sec "versions"
$BEND version; (cd bridge && lean --version); gcc --version | head -1; clang --version | head -1; python3 --version; uname -sm

sec "emit with gen.py (trusted) and compare with the committed emitted files"
T=$(mktemp -d)
for v in pos wrap buf l1 l2 ham osl; do ./gen.py ir/$v.json $T/$v > /dev/null; run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c variants/$v/i8dot.c && cmp $T/$v/prog.bend variants/$v/prog.bend"; done
for v in l2_badguard l2_buf ham_badguard osl_badguard osl_buf; do ./gen.py ir/$v.json $T/$v > /dev/null; run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c red/$v/i8dot.c && cmp $T/$v/prog.bend red/$v/prog.bend"; done
for v in l1_noabs ham_noabs osl_prepos; do ./gen.py ir/$v.json $T/$v > /dev/null; run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c controls/$v/i8dot.c && cmp $T/$v/prog.bend controls/$v/prog.bend"; done
run pos_C_byteidentical_to_r5 . 0 cmp variants/pos/i8dot.c $HOME/i8dot-bend-r5/variants/pos/i8dot.c
for v in pos wrap buf l1 l2 ham osl; do run kernel_copy_${v} . 0 cmp kernel.bend variants/$v/kernel.bend; done
sha256sum kernel.bend variants/*/prog.bend variants/*/i8dot.c

sec "Bend --verdict (actual kernel.bend + actual prog.bend)"
run bend_pos_PROOF variants/pos 0 $BEND PROOF.bend --verdict
for v in l1 l2 ham osl; do run bend_${v}_PROOF_RED variants/$v 0 $BEND PROOF_RED.bend --verdict; done

sec "trusted Bend->Lean translation: regenerate and require byte-identical Lean"
(cd bendlink && ./bend2lean.py kernel base.bend.pinned ../kernel.bend $T/BendKernel.lean && ./bend2lean.py progs $T/BendProgs.lean $(for v in pos wrap buf l1 l2 ham osl; do printf '%s=../variants/%s/prog.bend ' $v $v; done))
run base_pinned_same . 0 cmp bendlink/base.bend.pinned $HOME/.bend/bend2/base.bend
run translate_kernel_same . 0 cmp $T/BendKernel.lean bridge/Bridge/BendKernel.lean
run translate_progs_same . 0 cmp $T/BendProgs.lean bridge/Bridge/BendProgs.lean

sec "Lean build (checker + all proofs) and axiom audit"
run lean_build bridge 0 lake build
run lean_audit bridge 0 lake env lean Audit.lean
echo "audited theorems: $(grep -c '^#print' bridge/Audit.lean)"; grep -oE "\[[^]]*\]|does not depend on any axioms" $R/lean_audit.txt | sort | uniq -c
run no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" bridge/Bridge

sec "the one executable gate on the actual emitted files"
for v in $POS; do run gate_exact_$v . 0 $C exact variants/$v/i8dot.c variants/$v/prog.bend; run gate_match_$v . 0 $C match variants/$v/i8dot.c variants/$v/prog.bend; done
run gate_exact_wrap_own . 3 $C exact variants/wrap/i8dot.c variants/wrap/prog.bend
run gate_match_wrap_own . 0 $C match variants/wrap/i8dot.c variants/wrap/prog.bend
echo "-- base controls (three-kernel milestone)"
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
echo "-- Hamming / one-sided L1 controls"
run ctl_ham_bit_to_2 . 2 $C exact controls/ham_bit2/i8dot.c variants/ham/prog.bend
run ctl_osl_pos_to_1 . 2 $C exact controls/osl_pos1/i8dot.c variants/osl/prog.bend
run ctl_ham_wrong_guard_2147483648 . 2 $C exact red/ham_badguard/i8dot.c variants/ham/prog.bend
run ctl_ham_wrong_guard_match . 2 $C match red/ham_badguard/i8dot.c red/ham_badguard/prog.bend
run ctl_osl_wrong_guard_8421505 . 2 $C exact red/osl_badguard/i8dot.c variants/osl/prog.bend
run ctl_osl_missing_guard . 2 $C exact controls/osl_noguard/i8dot.c variants/osl/prog.bend
run ctl_buf_osl_diffbuffer . 2 $C exact red/osl_buf/i8dot.c red/osl_buf/prog.bend
run ctl_ham_noabs_exact_own . 3 $C exact controls/ham_noabs/i8dot.c controls/ham_noabs/prog.bend
run ctl_ham_noabs_match_own . 5 $C match controls/ham_noabs/i8dot.c controls/ham_noabs/prog.bend
run ctl_ham_noabs_vs_hamprog . 3 $C exact controls/ham_noabs/i8dot.c variants/ham/prog.bend
run ctl_osl_pos_before_sub_exact . 3 $C exact controls/osl_prepos/i8dot.c controls/osl_prepos/prog.bend
run ctl_osl_pos_before_sub_match . 5 $C match controls/osl_prepos/i8dot.c controls/osl_prepos/prog.bend
run ctl_osl_pos_before_sub_vs_osl . 3 $C exact controls/osl_prepos/i8dot.c variants/osl/prog.bend
run ctl_l1C_vs_hamprog . 3 $C exact variants/l1/i8dot.c variants/ham/prog.bend
run ctl_l1C_vs_oslprog . 3 $C exact variants/l1/i8dot.c variants/osl/prog.bend
run ctl_hamC_vs_oslprog . 3 $C exact variants/ham/i8dot.c variants/osl/prog.bend
run ctl_oslC_vs_l1prog . 3 $C exact variants/osl/i8dot.c variants/l1/prog.bend
run ctl_oslC_vs_hamprog . 3 $C exact variants/osl/i8dot.c variants/ham/prog.bend
for v in ham osl; do sed 's/^def prog()/def prog2()/' variants/$v/prog.bend > $T/tamper_$v.bend; run ctl_${v}prog_tampered . 4 $C exact variants/$v/i8dot.c $T/tamper_$v.bend; done

sec "negative controls: evaluator primitive changed in kernel.bend; Bend's law shares the primitive, the Lean link does not"
negctl() { local name=$1 var=$2 sedexpr=$3 N=$T/neg_$1; mkdir -p $N/$var
  sed "$sedexpr" kernel.bend > $N/kernel.bend
  run neg_${name}_kernel_changed . 1 cmp -s kernel.bend $N/kernel.bend
  cp variants/$var/prog.bend variants/$var/PROOF_RED.bend $N/$var/; cp $N/kernel.bend $N/$var/kernel.bend
  run neg_${name}_bend_${var}_law_still_passes $N/$var 0 $BEND PROOF_RED.bend --verdict
  (cd bendlink && ./bend2lean.py kernel base.bend.pinned $N/kernel.bend $N/BendKernel.lean) > /dev/null
  run neg_${name}_lean_differs . 1 cmp -s $N/BendKernel.lean bridge/Bridge/BendKernel.lean
  cp -a bridge $N/bridge; cp $N/BendKernel.lean $N/bridge/Bridge/BendKernel.lean
  run neg_${name}_link_build_fails $N/bridge 1 lake build Bridge.BendLink
  grep -m1 -oE "BendLink.lean:[0-9]+:[0-9]+: [a-z ]+" $R/neg_${name}_link_build_fails.txt; rm -rf $N/bridge; }
negctl zsub l1 's/Z{Nat.add(p, m), Nat.add(n, q)}/Z{Nat.add(p, q), Nat.add(n, m)}/'
negctl zpos osl '/^def zpos/,/^def / s/Z{Nat.sub(p, n), 0n}/Z{Nat.sub(n, p), 0n}/'
negctl zbit ham '/^def zbit.sel/,/^def zbit(/ s/Z{1n, 0n}/Z{2n, 0n}/'

sec "finite native differential tests (not proof): n=0, 1, 2, extremes, around each guard, deterministic random"
CAP=1048576
for v in pos:0:131071 l1:1:8421504 l2:2:33025 ham:3:2147483647 osl:4:8421504; do IFS=: read n k Nn <<< "$v"
  cap=; [ $n = ham ] && cap=$CAP
  for cc in "gcc -O2" "gcc -O3 -march=native" "clang -O3" "gcc -O1 -fsanitize=undefined -fno-sanitize-recover=all" "clang -O1 -fsanitize=undefined -fno-sanitize-recover=all"; do
    tag=$(echo "$cc" | tr -c 'a-zA-Z0-9\n' '_')
    run native_${n}_$tag native 0 sh -c "$cc -std=c11 -o t_$n test.c ../variants/$n/i8dot.c && ./t_$n $k $Nn $cap"; done; done
echo "-- Hamming at its exact guard with full 2 GiB readable arrays (one build): n = N-1, N on extremes (N*1 = INT32_MAX)"
run native_ham_fulledge_gcc_O2 native 0 sh -c "gcc -O2 -std=c11 -o t_hamfull test.c ../variants/ham/i8dot.c && ./t_hamfull 3 2147483647"
for o in $POS; do gcc -O2 -c -o $T/$o.o variants/$o/i8dot.c; echo "$o undefined symbols: [$(nm -u $T/$o.o | tr '\n' ' ')]"; done
rm -f native/t_*

sec "summary"
echo "TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
rm -rf "$T"
[ $UNEXPECTED = 0 ]
