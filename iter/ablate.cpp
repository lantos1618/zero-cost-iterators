#define main bench_main
#include "bench.cpp"
#undef main
// ablation: which proved step buys the speed?
NOINLINE Summ hand_amp(const std::vector<Emp>& es, u64 minSal, u64 pct) {   // hand loop, & instead of &&
  Summ s;
  for (const Emp& e : es) if (e.active & (e.salary >= minSal)) s = summStep(s, e.name, e.salary * pct / 100);
  return s;
}
NOINLINE Summ mask_inline(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // masked count/total, first/last kept in-loop
  Summ s; u64 c = 0, t = 0; std::size_t n = es.size(), fi = n, la = n;
  for (std::size_t i = 0; i < n; ++i) { const Emp& e = es[i]; bool k = e.active & (e.salary >= minSal);
    u64 m = 0 - (u64)k; c += 1 & m; t += (e.salary * pct / 100) & m; fi = (k & (fi == n)) ? i : fi; la = k ? i : la; }
  s.count = c; s.total = t; if (fi < n) s.first = es[fi].name; if (la < n) s.last = es[la].name; return s;
}
NOINLINE Summ split1(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // split + mask, 1 lane
  Summ s; u64 c = 0, t = 0; std::size_t n = es.size();
  for (std::size_t i = 0; i < n; ++i) { const Emp& e = es[i]; u64 m = 0 - (u64)(e.active & (e.salary >= minSal)); c += 1 & m; t += (e.salary * pct / 100) & m; }
  s.count = c; s.total = t;
  for (std::size_t j = 0; j < n; ++j) if (es[j].active & (es[j].salary >= minSal)) { s.first = es[j].name; break; }
  for (std::size_t j = n; j-- > 0;) if (es[j].active & (es[j].salary >= minSal)) { s.last = es[j].name; break; }
  return s;
}
NOINLINE Summ split1_andand(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // split1_mask, but && in the mask
  Summ s; u64 c = 0, t = 0; std::size_t n = es.size();
  for (std::size_t i = 0; i < n; ++i) { const Emp& e = es[i]; u64 m = 0 - (u64)(e.active && e.salary >= minSal); c += 1 & m; t += (e.salary * pct / 100) & m; }
  s.count = c; s.total = t;
  for (std::size_t j = 0; j < n; ++j) if (es[j].active & (es[j].salary >= minSal)) { s.first = es[j].name; break; }
  for (std::size_t j = n; j-- > 0;) if (es[j].active & (es[j].salary >= minSal)) { s.last = es[j].name; break; }
  return s;
}
NOINLINE Summ split_branchy(const std::vector<Emp>& es, u64 minSal, u64 pct) {  // split, 1 lane, if instead of mask
  Summ s; u64 c = 0, t = 0; std::size_t n = es.size();
  for (std::size_t i = 0; i < n; ++i) { const Emp& e = es[i]; if (e.active && e.salary >= minSal) { c += 1; t += e.salary * pct / 100; } }
  s.count = c; s.total = t;
  for (std::size_t j = 0; j < n; ++j) if (es[j].active && es[j].salary >= minSal) { s.first = es[j].name; break; }
  for (std::size_t j = n; j-- > 0;) if (es[j].active && es[j].salary >= minSal) { s.last = es[j].name; break; }
  return s;
}
int main() {
  std::size_t n = 1000000; std::vector<u64> xs; u64 s = 42;
  for (std::size_t i = 0; i < n; ++i) { s = s * 6364136223846793005ULL + 1442695040888963407ULL; xs.push_back(s >> 40); }
  static const std::string_view names[] = {"ana", "bo", "cy", "di", "ed", "flo", "gus", "hal"};
  std::vector<Emp> es(n), sorted;
  for (std::size_t i = 0; i < n; ++i) es[i] = {names[i % 8], xs[i] % 200000, xs[i] % 5 != 0};
  sorted = es; std::sort(sorted.begin(), sorted.end(), [](const Emp& a, const Emp& b) { return a.active != b.active ? a.active < b.active : a.salary < b.salary; });
  auto same = [](Summ a, Summ b) { return a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last; };
  for (auto* v : {&es, &sorted}) for (u64 ms : {0ull, 50000ull, 250000ull})
    if (!(same(handA(*v, ms, 90), hand_amp(*v, ms, 90)) && same(handA(*v, ms, 90), mask_inline(*v, ms, 90)) &&
          same(handA(*v, ms, 90), split1(*v, ms, 90)) && same(handA(*v, ms, 90), split1_andand(*v, ms, 90)) && same(handA(*v, ms, 90), split_branchy(*v, ms, 90)) && same(handA(*v, ms, 90), provedA(*v, ms, 90))))
      { std::printf("MISMATCH ms=%llu\n", (unsigned long long)ms); return 1; }
  for (int round = 1; round <= 2; ++round) for (int d = 0; d < 2; ++d) { const char* nm = d ? "sorted" : "random"; auto* v = d ? &sorted : &es;
    std::printf("-- round %d data=%s\n", round, nm);
    bench("handA", n, 20, [&](int r) { return handA(*v, 50000 + r % 2, 90).total; });
    bench("hand_amp", n, 20, [&](int r) { return hand_amp(*v, 50000 + r % 2, 90).total; });
    bench("split_branchy", n, 20, [&](int r) { return split_branchy(*v, 50000 + r % 2, 90).total; });
    bench("mask_inline", n, 20, [&](int r) { return mask_inline(*v, 50000 + r % 2, 90).total; });
    bench("split1_mask", n, 20, [&](int r) { return split1(*v, 50000 + r % 2, 90).total; });
    bench("split1_andand", n, 20, [&](int r) { return split1_andand(*v, 50000 + r % 2, 90).total; });
    bench("provedA_4lane", n, 20, [&](int r) { return provedA(*v, 50000 + r % 2, 90).total; });
  }
}
