# History

Reports and raw logs from the earlier milestones, kept as evidence. They describe the folder layout of commit
`bebd7da`, before files moved into `kernels/` and `history/`; the code they describe is now under `kernels/` and
`bridge/`, and its checks are in `kernels/replay.sh`.

| milestone | report |
|---|---|
| first zero-cost milestone: exact signed-INT8 dot product, Bend laws, C↔IR gate, INT8 benchmark | `README_v0_zero_cost.md` |
| i8red: one gate and one shared proof for three INT8 reductions | `README_i8red.md` |
| i8red5: five INT8 reductions, benchmarked against hand-written C | `README_i8red5.md` |
| i8red6: certified ternary-L1 and `!=`-Hamming spellings | `README_i8red6.md` |
| i8red7: `.loop()` front door generating all five kernels | `README_i8red7.md` |
| i8red8: typed lazy `.view()`, `.fuse()` / `.parallelize(...)`, APL reference models | `README_i8red8.md` |
| i8red9: generic typed `.view()` and stable `groupFold`; library benchmarks | `README_i8red9.md` |
| i8red10: the `tasks` CLI | now `../README.md` and `../docs/DETAILS.md` |

The other files are the raw evidence those reports cite: `EVIDENCE*.txt` (check outputs), `REPLAY*_clean.txt`
(clean replay transcripts; `REPLAY_attempt1_badpath.txt` is a failed first attempt kept on purpose),
`VERIFY_i8red.txt`, `BENCH_run*_log.txt` (INT8 benchmark runs) and `records/` (library benchmark logs, emitted C,
and the full i8red10 replay log).

`README_i8red8.md` includes results the user ran on a Mac (Bend, Lean tiling, Metal); those were not rerun in
Devin.
