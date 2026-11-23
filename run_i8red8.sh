#!/usr/bin/env bash
# i8red8 replay: everything i8red7 replays, PLUS the typed lazy .view() stream model, APL reference models,
# pure lambda subset, bytes/UTF-8 rows, and the .view() -> existing Pipe IR -> exact gate path.
# (i8red7 part:) .loop() front door + five scalar signed-INT8 reductions (dot, L1, squared L2, Hamming, one-sided L1) under one gate
# and one shared Lean induction. Raw outputs + exit codes -> results_i8red8/*.txt; summary on stdout (tee it).
# Needs: bend 2.0.40 (~/.bend/bin/bend), elan + leanprover/lean4:v4.15.0, gcc, clang, python3, ~5 GiB free RAM.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH BEND_NO_TELEMETRY=1
BEND=${BEND:-$HOME/.bend/bin/bend}
UNEXPECTED=0; TOTAL=0
R=$PWD/results_i8red8; rm -rf "$R"; mkdir -p "$R"
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
for v in l2_badguard l2_buf ham_badguard osl_badguard osl_buf l1_badguard l1_buf ham_buf; do ./gen.py ir/$v.json $T/$v > /dev/null; run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c red/$v/i8dot.c && cmp $T/$v/prog.bend red/$v/prog.bend"; done
for v in l1_noabs ham_noabs osl_prepos ham_nosub; do ./gen.py ir/$v.json $T/$v > /dev/null; run emit_${v}_same . 0 sh -c "cmp $T/$v/i8dot.c controls/$v/i8dot.c && cmp $T/$v/prog.bend controls/$v/prog.bend"; done
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
(cd bendlink && ./bend2lean.py progs $T/BendGen.lean $(for v in dot l1 l2 ham osl qz7; do printf 'g%s=../gen7/%s/prog.bend ' $v $v; done)) > /dev/null
run translate_gen7_progs_same . 0 cmp $T/BendGen.lean bridge/Pipe/BendGen.lean

sec "Lean build (checker + all proofs) and axiom audit"
run lean_build bridge 0 lake build
run lean_audit bridge 0 lake env lean Audit.lean
echo "audited theorems: $(grep -c '^#print' bridge/Audit.lean)"; grep -oE "\[[^]]*\]|does not depend on any axioms" $R/lean_audit.txt | sort | uniq -c
run audit_covers_every_theorem . 0 sh -c "[ \$(grep -c '^#print' bridge/Audit.lean) = \$(cat bridge/Bridge/Proofs.lean bridge/Bridge/BendLink.lean bridge/Pipe/Core.lean bridge/Pipe/Facts.lean bridge/Pipe/GenLink.lean | grep -cE '^\s*(private )?theorem ') ]"
run no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" bridge/Bridge bridge/Pipe bridge/PipeGen.lean

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

echo "-- i8red6: certified ternary L1 (AbsT) and != Hamming (Ne0) spellings"
for m in l1t_inverted l1t_gt l1t_le l1t_bothneg l1t_noguard; do run ctl6_$m . 2 $C exact controls/$m/i8dot.c variants/l1/prog.bend; done
for m in ham_eq ham_gt ham_ne1 ham_noguard; do run ctl6_$m . 2 $C exact controls/$m/i8dot.c variants/ham/prog.bend; done
run ctl6_l1_wrong_guard_8421505 . 2 $C exact red/l1_badguard/i8dot.c variants/l1/prog.bend
run ctl6_l1_wrong_guard_match . 2 $C match red/l1_badguard/i8dot.c red/l1_badguard/prog.bend
run ctl6_buf_l1_absbuffer . 2 $C exact red/l1_buf/i8dot.c red/l1_buf/prog.bend
run ctl6_buf_ham_ne0buffer . 2 $C exact red/ham_buf/i8dot.c red/ham_buf/prog.bend
echo "   (sign-sensitive: Sub;Bit without Abs/Ne0 = controls/ham_noabs above: exact 3, match 5)"
run ctl6_ham_nosub_exact_own . 3 $C exact controls/ham_nosub/i8dot.c controls/ham_nosub/prog.bend
run ctl6_ham_nosub_match_own . 5 $C match controls/ham_nosub/i8dot.c controls/ham_nosub/prog.bend
run ctl6_ham_nosub_vs_hamprog . 3 $C exact controls/ham_nosub/i8dot.c variants/ham/prog.bend
for v in l1 ham; do R6=controls/${v}_retired
  run ctl6_${v}_retired_spelling_exact_own . 2 $C exact $R6/i8dot.c $R6/prog.bend
  run ctl6_${v}_retired_spelling_match_own . 2 $C match $R6/i8dot.c $R6/prog.bend
  run ctl6_${v}_retired_C_vs_new_prog . 2 $C exact $R6/i8dot.c variants/$v/prog.bend
  run ctl6_${v}_new_C_vs_retired_prog . 3 $C exact variants/$v/i8dot.c $R6/prog.bend; done
run ctl6_hamC_vs_l1prog . 3 $C exact variants/ham/i8dot.c variants/l1/prog.bend
run ctl6_hamC_vs_dotprog . 3 $C exact variants/ham/i8dot.c variants/pos/prog.bend
run ctl6_l1C_vs_dotprog . 3 $C exact variants/l1/i8dot.c variants/pos/prog.bend
sed 's/^def prog()/def prog2()/' variants/l1/prog.bend > $T/tamper_l1.bend; run ctl6_l1prog_tampered . 4 $C exact variants/l1/i8dot.c $T/tamper_l1.bend

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
negctl zne0 ham '/^def zne0.eq/,/^def zne0.sel/ s/Z{0n, 0n}/Z{1n, 0n}/'
negctl zabs l1 '/^def zabs/,/^def / s/Z{Nat.sub(p, n), 0n}/Z{Nat.sub(n, p), 0n}/'

sec "finite native differential tests (not proof): n=0, 1, 2, extremes, around each guard, deterministic random"
CAP=1048576
for v in pos:0:131071 l1:1:8421504 l2:2:33025 ham:3:2147483647 osl:4:8421504; do IFS=: read n k Nn <<< "$v"
  cap=; [ $n = ham ] && cap=$CAP
  for cc in "gcc -O2" "gcc -O3 -march=native" "clang -O3" "gcc -O1 -fsanitize=undefined -fno-sanitize-recover=all" "clang -O1 -fsanitize=undefined -fno-sanitize-recover=all"; do
    tag=$(echo "$cc" | tr -c 'a-zA-Z0-9\n' '_')
    run native_${n}_$tag native 0 sh -c "$cc -std=c11 -o t_$n test.c ../gen7/${n/pos/dot}/i8dot.c && ./t_$n $k $Nn $cap"; done; done
echo "-- Hamming at its exact guard with full 2 GiB readable arrays (one build): n = N-1, N on extremes (N*1 = INT32_MAX)"
run native_ham_fulledge_gcc_O2 native 0 sh -c "gcc -O2 -std=c11 -o t_hamfull test.c ../gen7/ham/i8dot.c && ./t_hamfull 3 2147483647"
for o in dot l1 l2 ham osl qz7; do gcc -O2 -c -o $T/$o.o gen7/$o/i8dot.c; echo "$o undefined symbols: [$(nm -u $T/$o.o | tr '\n' ' ')]"; run gen7_${o}_no_imports . 0 sh -c "[ -z \"\$(nm -u $T/$o.o)\" ]"; done
rm -f native/t_*

sec "i8red7: .loop() front door -> lowered one-loop IR -> emitted C + Bend (fresh), compared with committed gen7"
PG=$PWD/bridge/.lake/build/bin/pipegen
run pipegen_run . 0 $PG $T/gen7
cat $R/pipegen_run.txt
CTL="l1_drop_abs l1_abs_to_sq l1_extra_sq dot_to_sub dot_extra_abs ham_swap_order ham_mul_zip osl_to_abs osl_twice l2_to_mul"
for k in dot l1 l2 ham osl qz7; do run pipegen_${k}_same . 0 sh -c "cmp $T/gen7/$k/i8dot.c gen7/$k/i8dot.c && cmp $T/gen7/$k/prog.bend gen7/$k/prog.bend"; done
for k in $CTL; do run pipegen_ctl_${k}_same . 0 sh -c "cmp $T/gen7/controls/$k/i8dot.c gen7/controls/$k/i8dot.c && cmp $T/gen7/controls/$k/prog.bend gen7/controls/$k/prog.bend"; done
run gen7_hash_lock gen7 0 sha256sum -c SHA256SUMS
run generation_reads_no_old_IR . 1 grep -nE "posIR|l1IR|l2IR|hamIR|oslIR|wrapIR|\.json|readFile" bridge/Pipe/Core.lean bridge/Pipe/Emit.lean bridge/Pipe/Chains.lean bridge/PipeGen.lean
ctr() { run contract_$1_$2 . 0 sh -c "awk -v l='$1:' '\$1==l{f=1;n=0} f{n++; if(n==4){print; exit}}' $R/pipegen_run.txt | grep -q ': $2\$'"; }
for k in dot l1 l2 ham osl qz7 ham_swap_order osl_twice; do ctr $k OK; done
for k in l1_drop_abs l1_abs_to_sq l1_extra_sq dot_to_sub dot_extra_abs ham_mul_zip osl_to_abs l2_to_mul; do ctr $k FAIL; done

sec "gen7 vs i8red6: identical bytes except the provenance comment (C line 1, Bend line 4)"
for m in dot:pos l1:l1 l2:l2 ham:ham osl:osl qz7:l1; do g=${m%%:*}; o=${m##*:}
  run gen7_${g}_vs_i8red6_${o} . 0 bash -c "cmp <(tail -n +2 gen7/$g/i8dot.c) <(tail -n +2 $HOME/i8red6/variants/$o/i8dot.c) && cmp <(sed 4d gen7/$g/prog.bend) <(sed 4d $HOME/i8red6/variants/$o/prog.bend) && [ \$(diff gen7/$g/i8dot.c $HOME/i8red6/variants/$o/i8dot.c | grep -c '^[<>]') = 2 ]"; done
for g in dot l1 l2 ham osl qz7; do run gen7_kernel_copy_$g . 0 cmp kernel.bend gen7/$g/kernel.bend; done
run gen7_dot_PROOF_copy . 0 sh -c "cmp gen7/dot/PROOF.bend variants/pos/PROOF.bend && cmp gen7/dot/LAWS.bend variants/pos/LAWS.bend"
for m in l1:l1 l2:l2 ham:ham osl:osl qz7:l1; do run gen7_${m%%:*}_PROOF_RED_copy . 0 cmp gen7/${m%%:*}/PROOF_RED.bend variants/${m##*:}/PROOF_RED.bend; done

sec "actual Bend --verdict on the pipegen-emitted prog.bend files"
run bend_gen7_dot_PROOF gen7/dot 0 $BEND PROOF.bend --verdict
for v in l1 l2 ham osl qz7; do run bend_gen7_${v}_PROOF_RED gen7/$v 0 $BEND PROOF_RED.bend --verdict; done

sec "the same exact gate on the pipegen-emitted files"
for k in dot l1 l2 ham osl qz7; do run gate7_exact_$k . 0 $C exact gen7/$k/i8dot.c gen7/$k/prog.bend; run gate7_match_$k . 0 $C match gen7/$k/i8dot.c gen7/$k/prog.bend; done

sec "source-chain controls: well-typed edits (lowered program changes; gate and/or kernel contract decide)"
ge() { run gate7_ctl_$1_exact . $2 $C exact gen7/controls/$1/i8dot.c gen7/controls/$1/prog.bend; run gate7_ctl_$1_match . $3 $C match gen7/controls/$1/i8dot.c gen7/controls/$1/prog.bend; }
ge l1_drop_abs 2 2; ge l1_abs_to_sq 0 0; ge l1_extra_sq 2 2; ge dot_to_sub 2 2; ge dot_extra_abs 3 5
ge ham_swap_order 2 2; ge ham_mul_zip 2 2; ge osl_to_abs 0 0; ge osl_twice 2 2; ge l2_to_mul 2 2
echo "-- the two legitimately different valid chains pass as another kernel, and fail their intended kernel's pairing:"
run gate7_ctl_l1_abs_to_sq_vs_l1_prog . 3 $C exact gen7/controls/l1_abs_to_sq/i8dot.c gen7/l1/prog.bend
run gate7_ctl_osl_to_abs_vs_osl_prog . 3 $C exact gen7/controls/osl_to_abs/i8dot.c gen7/osl/prog.bend
run gate7_ctl_dot_extra_abs_vs_dot_prog . 3 $C exact gen7/controls/dot_extra_abs/i8dot.c gen7/dot/prog.bend
run gate7_gen_l1C_vs_gen_l2prog . 3 $C exact gen7/l1/i8dot.c gen7/l2/prog.bend
run gate7_gen_hamC_vs_gen_oslprog . 3 $C exact gen7/ham/i8dot.c gen7/osl/prog.bend
sed 's/^def prog()/def prog2()/' gen7/l1/prog.bend > $T/tamper_g7.bend; run gate7_gen_l1prog_tampered . 4 $C exact gen7/l1/i8dot.c $T/tamper_g7.bend

sec "source-chain controls: ill-typed chains must not elaborate (exit 1); the positive must (exit 0)"
run chain_type_ok_positive bridge 0 lake env lean ../pipe_controls/ok_positive.lean
for f in ty_missing_zip ty_map_before_zip ty_missing_terminal ty_stage_after_terminal ty_two_zips ty_terminal_first ty_double_terminal ty_unsupported_callback; do
  run chain_$f bridge 1 lake env lean ../pipe_controls/$f.lean; done

sec "i8red8: Vw stream model (view / fuse / parallelize), APL models, lambda subset, UTF-8: axiom audit"
VA=$R/vw_audit.txt
run vw_audit bridge 0 lake env lean VwAudit.lean
grep -E "^Vw theorems audited" $VA; grep -oE "\[[^]]*\]$" $VA | sort | uniq -c
run vw_audit_covers_every_theorem . 0 sh -c 'm=0; for n in $(cat bridge/Vw/*.lean | grep -oE "^\s*(private )?theorem [^ ]+" | awk "{print \$NF}"); do grep -qE "^AUDIT (.*\.)?$n Vw" '"$VA"' || { echo MISSING $n; m=1; }; done; echo "declared=$(cat bridge/Vw/*.lean | grep -cE "^\s*(private )?theorem ")"; exit $m'
run vw_no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" bridge/Vw bridge/Vw.lean bridge/VwTest.lean
run vw_no_maxheartbeats_zero . 1 grep -rn "maxHeartbeats 0" bridge/Vw

sec "i8red8: .view() entry point -> existing Pipe IR -> emitter -> exact gate (fresh pipegen output in \$T/gen7/view)"
grep -E "^view (entry|refusal)" $R/pipegen_run.txt
for k in dot l1 l2 ham osl; do
  run view_${k}_bytes_eq_loop_and_gen7 . 0 sh -c "cmp $T/gen7/view/$k/i8dot.c gen7/$k/i8dot.c && cmp $T/gen7/view/$k/prog.bend gen7/$k/prog.bend"
  run view_${k}_gate_exact . 0 $C exact $T/gen7/view/$k/i8dot.c $T/gen7/view/$k/prog.bend
  run view_${k}_inprocess_gate . 0 sh -c "awk '/^view entry $k:/{f=1} f&&/in-process exact gate/{print; exit}' $R/pipegen_run.txt | grep -q 'PASS (term = lower chain)'"; done
for k in dot_no_fuse dot_seed5; do run view_refusal_$k . 0 grep -q "view refusal $k: REFUSED as expected" $R/pipegen_run.txt; done
run view_dotC_vs_l1prog . 3 $C exact $T/gen7/view/dot/i8dot.c gen7/l1/prog.bend
run view_lean_positive bridge 0 lake env lean ../view_controls/ok_view_positive.lean
for f in ty_view_map_after_terminal ty_view_mapfn_before_zip ty_view_lambda_as_stage false_apl_truncating_zip false_apl_minus_left_fold false_apl_mask_drop false_unfused_c_lowering false_parallel_sub; do
  run view_ctl_$f bridge 1 lake env lean ../view_controls/$f.lean; done

sec "i8red8: actual Bend on the APL reference laws (apl_bend/AplView.bend) and its mutants"
run bend_apl_check apl_bend 0 $BEND AplView.bend
run bend_apl_verdict apl_bend 0 $BEND AplView.bend --verdict
run bend_apl_def_count . 0 sh -c "grep -cE '^def ' apl_bend/AplView.bend; grep -oE '^def [a-z_]+\([^)]*\) -> \{' apl_bend/AplView.bend | wc -l"
for f in reassoc minus_eq mask_drop scan_exclusive all_drop_pred dot_add_zip; do
  run bend_apl_neg_$f apl_bend/neg 1 $BEND $f.bend
  run bend_apl_neg_${f}_verdict apl_bend/neg 1 $BEND $f.bend --verdict; done

sec "i8red8: runtime tests (finite, not proof): UTF-8 vs Lean runtime, sort/groupBy/distinct vs independent refs, lambda C"
VT=$PWD/bridge/.lake/build/bin/vwtest
run vwtest . 0 $VT $T
cat $R/vwtest.txt
for cc in "gcc -O2 -Wall -Werror" "clang -O2 -Wall -Werror" "gcc -O1 -fsanitize=undefined -fno-sanitize-recover=all" "clang -O1 -fsanitize=undefined -fno-sanitize-recover=all"; do
  tag=$(echo "$cc" | tr -c 'a-zA-Z0-9\n' '_')
  run lam_c_$tag . 0 sh -c "$cc -std=c11 -o $T/lam_test $T/lam_test.c && $T/lam_test"; done

sec "summary"
echo "TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
rm -rf "$T"
[ $UNEXPECTED = 0 ]
