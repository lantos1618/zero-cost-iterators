#!/usr/bin/env bash
# Replays every documented `tasks` command against hand-written expected outputs (tasks/expected/*),
# byte for byte, plus the exit code. Run from the project root. Devin-only.
# Usage: tasks/replay.sh [BIN_DIR]   (default iter/.lake/build/bin)
set -u
cd "$(dirname "$0")/.."
B=${1:-iter/.lake/build/bin}
E=tasks/expected; F=tasks/fixtures
N=0; FAIL=0
c() { # name want_exit expected_stdout|- expected_stderr|- cmd...
  local name=$1 want=$2 eo=$3 ee=$4; shift 4
  local o e s; o=$(mktemp); e=$(mktemp)
  "$@" > "$o" 2> "$e"; s=$?
  local v=PASS
  [ "$s" = "$want" ] || v=FAIL
  [ "$eo" = - ] || cmp -s "$o" "$E/$eo" || v=FAIL
  [ "$ee" = - ] || cmp -s "$e" "$E/$ee" || v=FAIL
  [ "$eo" != - ] || [ ! -s "$o" ] || [ "$want" = 0 ] || [ "$want" = 1 ] || v=FAIL   # errors print nothing on stdout
  N=$((N+1)); [ $v = PASS ] || FAIL=$((FAIL+1))
  printf '\n--- [%s] %s\n$ %s\n' "$v" "$name" "${*#$B/}"
  sed 's/^/  stdout| /' "$o"; sed 's/^/  stderr| /' "$e"
  printf '  exit=%s want=%s stdout_vs=%s stderr_vs=%s\n' "$s" "$want" "$eo" "$ee"
  rm -f "$o" "$e"
}
T=$B/tasks
# 1. logsum
c logsum_default          0 access.out         -               $T logsum $F/access.log
c logsum_api_min100       0 access_api100.out  -               $T logsum $F/access.log --service api --min-latency 100
c logsum_warn             0 access_warn.out    -               $T logsum $F/access.log --level WARN
c logsum_all_filtered     0 access_nosuch.out  -               $T logsum $F/access.log --service nosuch
c logsum_exact_bignum     0 big.out            -               $T logsum $F/big.log
c logsum_empty_file       0 empty_log.out      -               $T logsum $F/empty.log
c logsum_bad_level        2 -                  bad_level.err   $T logsum $F/bad_level.log
c logsum_bad_latency      2 -                  bad_latency.err $T logsum $F/bad_latency.log
c logsum_invalid_utf8     2 -                  bad_utf8.err    $T logsum $F/bad_utf8.txt
c logsum_missing_file     2 -                  -               $T logsum $F/does_not_exist.log
c logsum_bad_flag_value  64 -                  -               $T logsum $F/access.log --min-latency abc
c logsum_bad_level_flag  64 -                  -               $T logsum $F/access.log --level DEBUG
# 2. sales
c sales_default           0 sales.out          -               $T sales $F/sales.csv
c sales_min_qty2          0 sales_min2.out     -               $T sales $F/sales.csv --min-qty 2
c sales_min_qty4          0 sales_min4.out     -               $T sales $F/sales.csv --min-qty 4
c sales_all_filtered      0 sales_min100.out   -               $T sales $F/sales.csv --min-qty 100
c sales_header_only       0 sales_header_only.out -            $T sales $F/sales_header_only.csv
c sales_empty_file        2 -                  sales_emptyfile.err $T sales $F/empty.log
c sales_no_header         2 -                  sales_noheader.err  $T sales $F/sales_noheader.csv
c sales_bad_qty           2 -                  sales_badqty.err    $T sales $F/sales_badqty.csv
c sales_quoted_field      2 -                  sales_quoted.err    $T sales $F/sales_quoted.csv
c sales_unknown_flag     64 -                  -               $T sales $F/sales.csv --bogus
# 3. manifest
c manifest_ok             0 manifest_ok.out    -               $T manifest $F/manifest_ok.txt
c manifest_ok_trace       0 manifest_ok.out    manifest_ok_trace.err    $T manifest $F/manifest_ok.txt --trace
c manifest_bad            1 manifest_bad.out   -               $T manifest $F/manifest_bad.txt
c manifest_bad_trace      1 manifest_bad.out   manifest_bad_trace.err   $T manifest $F/manifest_bad.txt --trace
c manifest_first_trace    1 manifest_first.out manifest_first_trace.err $T manifest $F/manifest_first.txt --trace
c manifest_blank_line     1 manifest_blank.out -               $T manifest $F/manifest_blank.txt
c manifest_empty_file     0 manifest_empty.out -               $T manifest $F/empty.log
c manifest_invalid_utf8   2 -                  bad_utf8.err    $T manifest $F/bad_utf8.txt
c eager_control_traces_all 0 eager_bad.out     eager_bad.err   $B/taskcheck eager $F/manifest_bad.txt
# usage
c usage_no_args          64 -                  -               $T
c usage_unknown_command  64 -                  -               $T frobnicate $F/access.log
c usage_missing_file     64 -                  -               $T sales
printf '\nTASKS_REPLAY cases=%s fails=%s\n' "$N" "$FAIL"
[ "$FAIL" = 0 ]
