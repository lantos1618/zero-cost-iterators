// The cheapest way to prove "ours ties or beats hand-written C++" wrong: time ours against the plain hand
// loop and the branch-free hand loop (bf*) on every workload, under any compiler and flags. falsify.sh runs it
// across compilers and prints a verdict per row. No <ranges>, so clang builds it too.
#include "common.hpp"

int main(int argc, char** argv) {
  std::size_t n = argc > 1 ? std::strtoull(argv[1], nullptr, 10) : 1000000;
  Data d = makeData(n);
  tuneAll(d);
  const auto& xs = d.xs;
  auto same = [](Summ a, Summ b) { return a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last; };
  bool ok = true;
  for (u64 k : {1ull, 2ull, 7ull})
    ok = ok && bfU(xs, k) == handU(xs, k) && provedU(xs, k) == handU(xs, k) && bfC(xs, k) == handC(xs, k) &&
         provedC(xs, k) == handC(xs, k) && bfMax(xs, k) == handMax(xs, k) && provedMax(xs, k) == handMax(xs, k);
  for (auto* rows : {&d.es, &d.sorted, &d.runs, &d.mixed})
    for (u64 m : {0ull, 50000ull, 250000ull})
      ok = ok && same(bfA(*rows, m, 90), handA(*rows, m, 90)) && same(adaptA(*rows, m, 90), handA(*rows, m, 90));
  ok = ok && provedF(xs, d.big) == handF(xs, d.big) && !provedF(xs, d.big + 1);
  std::printf("FALSIFY results_equal=%s\n", ok ? "true" : "false");
  if (!ok) return 1;

  const int reps = 20;
  bench("sum/hand", n, reps, [&](int r) { return handU(xs, r); });
  bench("sum/bf", n, reps, [&](int r) { return bfU(xs, r); });
  bench("sum/ours", n, reps, [&](int r) { return provedU(xs, r); });
  bench("count/hand", n, reps, [&](int r) { return handC(xs, r); });
  bench("count/bf", n, reps, [&](int r) { return bfC(xs, r); });
  bench("count/ours", n, reps, [&](int r) { return provedC(xs, r); });
  bench("max/hand", n, reps, [&](int r) { return handMax(xs, r).value_or(0); });
  bench("max/bf", n, reps, [&](int r) { return bfMax(xs, r).value_or(0); });
  bench("max/ours", n, reps, [&](int r) { return provedMax(xs, r).value_or(0); });
  const std::pair<const char*, const std::vector<Emp>*> rowSets[] = {
      {"records_random", &d.es}, {"records_sorted", &d.sorted}, {"records_runs", &d.runs}, {"records_mixed", &d.mixed}};
  for (const auto& set : rowSets) {
    const std::vector<Emp>* rows = set.second;
    std::string base = set.first;
    bench((base + "/hand").c_str(), n, reps, [&](int r) { return handA(*rows, 50000 + r % 2, 90).total; });
    bench((base + "/bf").c_str(), n, reps, [&](int r) { return bfA(*rows, 50000 + r % 2, 90).total; });
    bench((base + "/ours").c_str(), n, reps, [&](int r) { return adaptA(*rows, 50000 + r % 2, 90).total; });
  }
  bench("find_miss/hand", n, reps, [&](int r) { auto h = handF(xs, d.big + 1 + r); return h ? h->second : 0; });
  bench("find_miss/ours", n, reps, [&](int r) { auto h = provedF(xs, d.big + 1 + r); return h ? h->second : 0; });
  return 0;
}
