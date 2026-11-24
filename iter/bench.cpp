// C++20 baseline for Bench.lean: the same data and the same three pipelines, each written three ways:
// a hand loop, a lazy std::views chain (fused, like Iter), an eager std::vector per stage (staged), and a
// "proved" loop that applies rewrites proved in iter/Iter/Rewrite.lean.
// Build: g++ -O2 -std=c++20 bench.cpp -o bench_cpp
#include <ranges>

#include "common.hpp"

namespace v = std::views;

// filter -> map -> fold over words
NOINLINE u64 viewsU(const std::vector<u64>& xs, u64 k) {
  u64 acc = 0;
  for (u64 y : xs | v::filter([k](u64 x) { return (x ^ k) % 3 == 0; }) | v::transform([](u64 x) { return x * 2; }))
    acc += y;
  return acc;
}
NOINLINE u64 eagerU(const std::vector<u64>& xs, u64 k) {
  std::vector<u64> kept;
  std::copy_if(xs.begin(), xs.end(), std::back_inserter(kept), [k](u64 x) { return (x ^ k) % 3 == 0; });
  std::vector<u64> doubled(kept.size());
  std::transform(kept.begin(), kept.end(), doubled.begin(), [](u64 x) { return x * 2; });
  return std::accumulate(doubled.begin(), doubled.end(), u64{0});
}

// filter -> count and filter -> map -> max over words
NOINLINE u64 viewsC(const std::vector<u64>& xs, u64 k) {
  return (u64)std::ranges::distance(xs | v::filter([k](u64 x) { return (x ^ k) % 3 == 0; }));
}
NOINLINE std::optional<u64> viewsMax(const std::vector<u64>& xs, u64 k) {
  auto r = xs | v::filter([k](u64 x) { return (x ^ k) % 3 == 0; }) | v::transform([](u64 x) { return x * 2; });
  auto it = std::ranges::max_element(r);
  return it == r.end() ? std::nullopt : std::optional<u64>(*it);
}

// records: filter -> map to a pair -> fold into a summary
NOINLINE Summ viewsA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  Summ s;
  for (auto [name, pay] : es | v::filter([minSal](const Emp& e) { return e.active && e.salary >= minSal; })
                              | v::transform([pct](const Emp& e) { return std::pair{e.name, e.salary * pct / 100}; }))
    s = summStep(s, name, pay);
  return s;
}
NOINLINE Summ eagerA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  std::vector<Emp> kept;
  std::copy_if(es.begin(), es.end(), std::back_inserter(kept), [minSal](const Emp& e) { return e.active && e.salary >= minSal; });
  std::vector<std::pair<std::string_view, u64>> rows(kept.size());
  std::transform(kept.begin(), kept.end(), rows.begin(), [pct](const Emp& e) { return std::pair{e.name, e.salary * pct / 100}; });
  Summ s;
  for (auto [name, pay] : rows) s = summStep(s, name, pay);
  return s;
}

// enumerate -> find (early exit)
NOINLINE Hit viewsF(const std::vector<u64>& xs, u64 t) {
  auto numbered = v::iota(std::size_t{0}, xs.size()) | v::transform([&xs](std::size_t i) { return std::pair{i, xs[i]}; });
  auto it = std::ranges::find_if(numbered, [t](auto p) { return p.second > t; });
  return it == numbered.end() ? Hit{} : Hit{*it};
}
NOINLINE Hit eagerF(const std::vector<u64>& xs, u64 t) {
  std::vector<std::pair<std::size_t, u64>> numbered(xs.size());
  for (std::size_t i = 0; i < xs.size(); ++i) numbered[i] = {i, xs[i]};
  auto it = std::find_if(numbered.begin(), numbered.end(), [t](auto p) { return p.second > t; });
  return it == numbered.end() ? Hit{} : Hit{*it};
}

int main(int argc, char** argv) {
  std::size_t n = argc > 1 ? std::strtoull(argv[1], nullptr, 10) : 1000000;
  Data d = makeData(n);
  const auto& xs = d.xs;
  const auto &es = d.es, &sorted = d.sorted, &runs = d.runs, &mixed = d.mixed;
  const u64 big = d.big;
  tuneAll(d);

  auto same = [](Summ a, Summ b) { return a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last; };
  bool ok = handU(xs, 1) == viewsU(xs, 1) && handU(xs, 1) == eagerU(xs, 1) &&
            same(handA(es, 50000, 90), viewsA(es, 50000, 90)) && same(handA(es, 50000, 90), eagerA(es, 50000, 90)) &&
            handF(xs, big) == viewsF(xs, big) && handF(xs, big) == eagerF(xs, big) && !viewsF(xs, big + 1) &&
            handU(xs, 1) == provedU(xs, 1) && handU(xs, 2) == provedU(xs, 2) && handU(xs, 7) == provedU(xs, 7) &&
            handF(xs, big) == provedF(xs, big) && handF(xs, xs[999]) == provedF(xs, xs[999]) && !provedF(xs, big + 1) &&
            same(handA(es, 50000, 90), provedA(es, 50000, 90)) && same(handA(es, 250000, 90), provedA(es, 250000, 90)) &&
            same(handA(sorted, 50000, 90), viewsA(sorted, 50000, 90)) && same(handA(sorted, 50000, 90), provedA(sorted, 50000, 90)) &&
            same(handA(runs, 50000, 90), viewsA(runs, 50000, 90)) && same(handA(runs, 50000, 90), provedA(runs, 50000, 90)) &&
            same(handA(mixed, 50000, 90), viewsA(mixed, 50000, 90)) && same(handA(mixed, 50000, 90), provedA(mixed, 50000, 90));
  for (u64 k : {1ull, 2ull, 7ull})
    ok = ok && handC(xs, k) == viewsC(xs, k) && handC(xs, k) == provedC(xs, k) &&
         handMax(xs, k) == viewsMax(xs, k) && handMax(xs, k) == provedMax(xs, k);
  for (u64 k : {1ull, 2ull, 7ull}) {
    for (auto& c : provedU_cands) ok = ok && c.f(xs, k) == handU(xs, k);
    for (auto& c : provedC_cands) ok = ok && c.f(xs, k) == handC(xs, k);
  }
  for (auto& c : provedF_cands) ok = ok && c.f(xs, big) == handF(xs, big) && c.f(xs, xs[999]) == handF(xs, xs[999]) && !c.f(xs, big + 1);
  ok = ok && !provedMax(std::vector<u64>{1, 4}, 0) && provedC(std::vector<u64>{}, 0) == 0;
  for (auto* d : {&es, &sorted, &runs, &mixed}) for (u64 m : {0ull, 50000ull, 250000ull}) ok = ok && same(handA(*d, m, 90), adaptA(*d, m, 90));
  std::printf("BENCH cpp items=%zu results_equal=%s\n", n, ok ? "true" : "false");

  const int reps = 20;
  auto hitVal = [](Hit h) { return h ? h->second : u64{0}; };
  for (int round = 1; round <= 2; ++round) {
    std::printf("BENCH cpp round=%d\n", round);
    bench("cpp_handU", n, reps, [&](int r) { return handU(xs, r); });
    bench("cpp_viewsU", n, reps, [&](int r) { return viewsU(xs, r); });
    bench("cpp_eagerU", n, reps, [&](int r) { return eagerU(xs, r); });
    bench("cpp_provedU", n, reps, [&](int r) { return provedU(xs, r); });
    bench("cpp_handC", n, reps, [&](int r) { return handC(xs, r); });
    bench("cpp_viewsC", n, reps, [&](int r) { return viewsC(xs, r); });
    bench("cpp_provedC", n, reps, [&](int r) { return provedC(xs, r); });
    bench("cpp_handMax", n, reps, [&](int r) { return handMax(xs, r).value_or(0); });
    bench("cpp_viewsMax", n, reps, [&](int r) { return viewsMax(xs, r).value_or(0); });
    bench("cpp_provedMax", n, reps, [&](int r) { return provedMax(xs, r).value_or(0); });
    bench("cpp_handA", n, reps, [&](int r) { return handA(es, 50000 + r % 2, 90).total; });
    bench("cpp_viewsA", n, reps, [&](int r) { return viewsA(es, 50000 + r % 2, 90).total; });
    bench("cpp_eagerA", n, reps, [&](int r) { return eagerA(es, 50000 + r % 2, 90).total; });
    bench("cpp_provedA", n, reps, [&](int r) { return provedA(es, 50000 + r % 2, 90).total; });
    bench("cpp_adaptA", n, reps, [&](int r) { return adaptA(es, 50000 + r % 2, 90).total; });
    bench("cpp_handA_sorted", n, reps, [&](int r) { return handA(sorted, 50000 + r % 2, 90).total; });
    bench("cpp_viewsA_sorted", n, reps, [&](int r) { return viewsA(sorted, 50000 + r % 2, 90).total; });
    bench("cpp_provedA_sorted", n, reps, [&](int r) { return provedA(sorted, 50000 + r % 2, 90).total; });
    bench("cpp_adaptA_sorted", n, reps, [&](int r) { return adaptA(sorted, 50000 + r % 2, 90).total; });
    bench("cpp_handA_runs", n, reps, [&](int r) { return handA(runs, 50000 + r % 2, 90).total; });
    bench("cpp_viewsA_runs", n, reps, [&](int r) { return viewsA(runs, 50000 + r % 2, 90).total; });
    bench("cpp_provedA_runs", n, reps, [&](int r) { return provedA(runs, 50000 + r % 2, 90).total; });
    bench("cpp_adaptA_runs", n, reps, [&](int r) { return adaptA(runs, 50000 + r % 2, 90).total; });
    bench("cpp_handA_mixed", n, reps, [&](int r) { return handA(mixed, 50000 + r % 2, 90).total; });
    bench("cpp_viewsA_mixed", n, reps, [&](int r) { return viewsA(mixed, 50000 + r % 2, 90).total; });
    bench("cpp_provedA_mixed", n, reps, [&](int r) { return provedA(mixed, 50000 + r % 2, 90).total; });
    bench("cpp_adaptA_mixed", n, reps, [&](int r) { return adaptA(mixed, 50000 + r % 2, 90).total; });
    bench("cpp_handF_miss", n, reps, [&](int r) { return hitVal(handF(xs, big + 1 + r)); });
    bench("cpp_viewsF_miss", n, reps, [&](int r) { return hitVal(viewsF(xs, big + 1 + r)); });
    bench("cpp_eagerF_miss", n, reps, [&](int r) { return hitVal(eagerF(xs, big + 1 + r)); });
    bench("cpp_provedF_miss", n, reps, [&](int r) { return hitVal(provedF(xs, big + 1 + r)); });
  }
  return ok ? 0 : 1;
}
