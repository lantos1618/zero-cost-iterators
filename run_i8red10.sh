#!/usr/bin/env bash
# i8red10 replay: the full i8red9 replay (unchanged, ./run_i8red9.sh -> results_i8red9/), THEN the everyday
# `tasks` CLI: TaskCore build + axiom audit, no-sorry scan, 300-input fixed-seed reference/mutant check per task,
# and the 34-command fixture replay against hand-written expected outputs (tasks/replay.sh).
# Devin-only rule: every build, proof check, test and replay runs inside the Devin workspace.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH
./run_i8red9.sh; PREV=$?
UNEXPECTED=0; TOTAL=0
R=$PWD/results_i8red10; rm -rf "$R"; mkdir -p "$R"
sec() { printf '\n==================== %s\n' "$1"; }
run() { local n=$1 d=$2 want=$3; shift 3; (cd "$d" && "$@") > "$R/$n.txt" 2>&1; local s=$?
  echo "exit=$s" >> "$R/$n.txt"; TOTAL=$((TOTAL+1)); local tag=ok; [ "$s" = "$want" ] || { tag=UNEXPECTED; UNEXPECTED=$((UNEXPECTED+1)); }
  printf '%-34s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -E 'audited|TASKCHECK fails|TASKS_REPLAY|error' "$R/$n.txt" | tail -1 | cut -c1-100)"; }
sec "i8red10: everyday tasks CLI"
run tasks_build bridge 0 lake build TaskCore tasks taskcheck
run taskcore_audit bridge 0 lake env lean TaskAudit.lean
run tasks_theorems_listed . 0 sh -c 'for n in logPipe_spec salesPipe_spec salesPipe_keys manifestPipe_spec entryBad_trace; do grep -E "^AUDIT Tasks\.$n TaskCore \[" results_i8red10/taskcore_audit.txt || { echo MISSING $n; exit 1; }; done'
run tasks_no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" bridge/TaskCore.lean bridge/Tasks.lean bridge/TaskCheck.lean
run taskcheck_generated . 0 bridge/.lake/build/bin/taskcheck
cat "$R/taskcheck_generated.txt"
run tasks_fixture_replay . 0 tasks/replay.sh
grep -E '^--- |TASKS_REPLAY' "$R/tasks_fixture_replay.txt"
sec "summary"
echo "i8red9 suite exit=$PREV (see its TOTAL/UNEXPECTED line above)"
echo "i8red10 TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
[ $PREV = 0 ] && [ $UNEXPECTED = 0 ]
