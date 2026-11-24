#define main bench_main
#include "bench.cpp"
#undef main
// Ablation of the record summary: which change buys the speed, and does it depend on the data?
NOINLINE Summ hand_amp(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // hand loop, & instead of &&
  Summ s;
  for (const Emp& e : es) if (e.active & (e.salary >= minSal)) s = summStep(s, e.name, e.salary * pct / 100);
  return s;
}
static void searches(Summ& s, const std::vector<Emp>& es, u64 minSal) {  // first / last as two early-exit searches
  for (std::size_t j = 0; j < es.size(); ++j) if (es[j].active & (es[j].salary >= minSal)) { s.first = es[j].name; break; }
  for (std::size_t j = es.size(); j-- > 0;) if (es[j].active & (es[j].salary >= minSal)) { s.last = es[j].name; break; }
}
NOINLINE Summ mask_ct(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // masked count/total pass only (no first/last)
  Summ s; u64 c = 0, t = 0;
  for (const Emp& e : es) { u64 m = 0 - (u64)(e.active & (e.salary >= minSal)); c += 1 & m; t += (e.salary * pct / 100) & m; }
  s.count = c; s.total = t; return s;
}
NOINLINE Summ split_mask(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // mask_ct + the two searches (old generated shape, 1 lane)
  Summ s = mask_ct(es, minSal, pct); searches(s, es, minSal); return s;
}
NOINLINE Summ split_andand(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // split_mask, but && in the mask
  Summ s; u64 c = 0, t = 0;
  for (const Emp& e : es) { u64 m = 0 - (u64)(e.active && e.salary >= minSal); c += 1 & m; t += (e.salary * pct / 100) & m; }
  s.count = c; s.total = t; searches(s, es, minSal); return s;
}
NOINLINE Summ split_branchy(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // split, if instead of mask
  Summ s; u64 c = 0, t = 0;
  for (const Emp& e : es) if (e.active && e.salary >= minSal) { c += 1; t += e.salary * pct / 100; }
  s.count = c; s.total = t; searches(s, es, minSal); return s;
}
NOINLINE Summ searches_only(const std::vector<Emp>& es, u64 minSal, u64) {  // just the two searches
  Summ s; searches(s, es, minSal); return s;
}
int main() {
  std::size_t n = 1000000; std::vector<u64> xs; u64 s = 42;
  for (std::size_t i = 0; i < n; ++i) { s = s * 6364136223846793005ULL + 1442695040888963407ULL; xs.push_back(s >> 40); }
  static const std::string_view names[] = {"ana", "bo", "cy", "di", "ed", "flo", "gus", "hal"};
  std::vector<Emp> es(n);
  for (std::size_t i = 0; i < n; ++i) es[i] = {names[i % 8], xs[i] % 200000, xs[i] % 5 != 0};
  std::vector<Emp> sorted = sortedRows(es);
  auto same = [](Summ a, Summ b) { return a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last; };
  for (auto* v : {&es, &sorted}) for (u64 ms : {0ull, 50000ull, 250000ull}) {
    Summ h = handA(*v, ms, 90), ct = mask_ct(*v, ms, 90), so = searches_only(*v, ms, 90);
    if (!(same(h, hand_amp(*v, ms, 90)) && same(h, split_mask(*v, ms, 90)) && same(h, split_andand(*v, ms, 90)) &&
          same(h, split_branchy(*v, ms, 90)) && same(h, provedA(*v, ms, 90)) && ct.count == h.count && ct.total == h.total &&
          so.first == h.first && so.last == h.last))
      { std::printf("MISMATCH ms=%llu\n", (unsigned long long)ms); return 1; }
  }
  std::printf("BENCH ablate results_equal=true\n");
  for (int round = 1; round <= 2; ++round) for (int d = 0; d < 2; ++d) {
    const char* nm = d ? "sorted" : "random"; auto* v = d ? &sorted : &es;
    std::printf("BENCH ablate round=%d data=%s\n", round, nm);
    auto row = [&](const char* label, auto f) { bench(label, n, 20, [&](int r) { Summ q = f(*v, 50000 + r % 2, 90); return q.total + q.count + q.first.size() + q.last.size(); }); };
    row("handA", handA); row("hand_amp", hand_amp); row("split_branchy", split_branchy); row("split_andand", split_andand);
    row("split_mask", split_mask); row("mask_ct", mask_ct); row("searches_only", searches_only); row("provedA", provedA);
  }
}
