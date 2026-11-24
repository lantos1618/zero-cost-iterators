// C++20 baseline for Bench.lean: the same data and the same three pipelines, each written three ways:
// a hand loop, a lazy std::views chain (fused, like Iter), an eager std::vector per stage (staged), and a
// "proved" loop that applies rewrites proved in iter/Iter/Rewrite.lean.
// Build: g++ -O2 -std=c++20 bench.cpp -o bench_cpp
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <optional>
#include <ranges>
#include <string_view>
#include <utility>
#include <vector>

#define NOINLINE __attribute__((noinline))
using u64 = std::uint64_t;
namespace v = std::views;

struct Emp { std::string_view name; u64 salary; bool active; };
struct Summ { u64 count = 0, total = 0; std::string_view first, last; };
using Hit = std::optional<std::pair<std::size_t, u64>>;

static Summ summStep(Summ s, std::string_view name, u64 pay) {
  if (s.count == 0) s.first = name;
  s.count += 1; s.total += pay; s.last = name;
  return s;
}

// filter -> map -> fold over words
NOINLINE u64 handU(const std::vector<u64>& xs, u64 k) {
  u64 acc = 0;
  for (u64 x : xs) if ((x ^ k) % 3 == 0) acc += x * 2;
  return acc;
}
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

// records: filter -> map to a pair -> fold into a summary
NOINLINE Summ handA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  Summ s;
  for (const Emp& e : es) if (e.active && e.salary >= minSal) s = summStep(s, e.name, e.salary * pct / 100);
  return s;
}
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
NOINLINE Hit handF(const std::vector<u64>& xs, u64 t) {
  for (std::size_t i = 0; i < xs.size(); ++i) if (xs[i] > t) return std::pair{i, xs[i]};
  return std::nullopt;
}
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


// Proved rewrites (iter/Iter/Rewrite.lean), written by hand in C++: the filter becomes a bit-mask select
// (sum_select, select_mask), the sum is split over 4 independent accumulators, item j in lane j % 4
// (sum_lanes), and the summary's first/last become a forward and a backward search (summary_split,
// head_filter, getLast_filter). The proofs cover + on 64-bit words; the C++ transcription is checked by the
// results_equal test, not proved.
NOINLINE u64 provedU(const std::vector<u64>& xs, u64 k) {
  // 8 lanes (sum_lanes), branch-free mask (sum_select, select_mask), and the map's *2 applied once to the
  // total instead of per item (sum_mul)
  u64 acc[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  std::size_t n = xs.size(), i = 0;
  for (; i + 8 <= n; i += 8)
    for (int j = 0; j < 8; ++j) { u64 x = xs[i + j]; acc[j] += x & (0 - (u64)((x ^ k) % 3 == 0)); }
  for (; i < n; ++i) { u64 x = xs[i]; acc[i % 8] += x & (0 - (u64)((x ^ k) % 3 == 0)); }
  u64 total = 0;
  for (u64 a : acc) total += a;
  return 2 * total;
}
NOINLINE Summ provedA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  auto keep = [minSal](const Emp& e) { return e.active & (e.salary >= minSal); };  // & not &&: no branch
  u64 cnt[4] = {0, 0, 0, 0}, tot[4] = {0, 0, 0, 0};
  std::size_t n = es.size(), i = 0;
  auto add = [&](std::size_t lane, const Emp& e) {
    u64 m = 0 - (u64)keep(e);
    cnt[lane] += 1 & m;
    tot[lane] += (e.salary * pct / 100) & m;
  };
  for (; i + 4 <= n; i += 4) for (int j = 0; j < 4; ++j) add(j, es[i + j]);
  for (; i < n; ++i) add(i % 4, es[i]);
  Summ s;
  s.count = cnt[0] + cnt[1] + cnt[2] + cnt[3];
  s.total = tot[0] + tot[1] + tot[2] + tot[3];
  for (std::size_t j = 0; j < n; ++j) if (keep(es[j])) { s.first = es[j].name; break; }
  for (std::size_t j = n; j-- > 0;) if (keep(es[j])) { s.last = es[j].name; break; }
  return s;
}

NOINLINE Hit provedF(const std::vector<u64>& xs, u64 t) {
  // blocks of 32 (find_blocks): a branch-free "any match?" per block, then a search inside the one block that has it
  constexpr std::size_t B = 32;
  std::size_t n = xs.size(), i = 0;
  for (; i + B <= n; i += B) {
    u64 any = 0;
    for (std::size_t j = 0; j < B; ++j) any |= (u64)(xs[i + j] > t);
    if (any) for (std::size_t j = 0; j < B; ++j) if (xs[i + j] > t) return std::pair{i + j, xs[i + j]};
  }
  for (; i < n; ++i) if (xs[i] > t) return std::pair{i, xs[i]};
  return std::nullopt;
}

template <class F>
static void bench(const char* label, std::size_t n, int reps, F f) {
  volatile u64 warm = f(0); (void)warm;
  std::vector<long long> ts;
  u64 chk = 0;
  for (int b = 0; b < 5; ++b) {
    auto t0 = std::chrono::steady_clock::now();
    u64 acc = 0;
    for (int r = 0; r < reps; ++r) acc += f(r);
    auto t1 = std::chrono::steady_clock::now();
    ts.push_back(std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count());
    chk = acc;
  }
  std::sort(ts.begin(), ts.end());
  std::printf("BENCH %s median_ns_per_item_x100=%lld checksum=%llu\n", label,
              ts[2] * 100 / (long long)(n * reps), (unsigned long long)chk);
}

int main(int argc, char** argv) {
  std::size_t n = argc > 1 ? std::strtoull(argv[1], nullptr, 10) : 1000000;
  std::vector<u64> xs;
  xs.reserve(n);
  u64 s = 42;
  for (std::size_t i = 0; i < n; ++i) { s = s * 6364136223846793005ULL + 1442695040888963407ULL; xs.push_back(s >> 40); }
  static const std::string_view names[] = {"ana", "bo", "cy", "di", "ed", "flo", "gus", "hal"};
  std::vector<Emp> es(n);
  for (std::size_t i = 0; i < n; ++i) es[i] = {names[i % 8], xs[i] % 200000, xs[i] % 5 != 0};
  u64 big = *std::max_element(xs.begin(), xs.end());

  auto same = [](Summ a, Summ b) { return a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last; };
  bool ok = handU(xs, 1) == viewsU(xs, 1) && handU(xs, 1) == eagerU(xs, 1) &&
            same(handA(es, 50000, 90), viewsA(es, 50000, 90)) && same(handA(es, 50000, 90), eagerA(es, 50000, 90)) &&
            handF(xs, big) == viewsF(xs, big) && handF(xs, big) == eagerF(xs, big) && !viewsF(xs, big + 1) &&
            handU(xs, 1) == provedU(xs, 1) && handU(xs, 2) == provedU(xs, 2) && handU(xs, 7) == provedU(xs, 7) &&
            handF(xs, big) == provedF(xs, big) && handF(xs, xs[999]) == provedF(xs, xs[999]) && !provedF(xs, big + 1) &&
            same(handA(es, 50000, 90), provedA(es, 50000, 90)) && same(handA(es, 250000, 90), provedA(es, 250000, 90));
  std::printf("BENCH cpp items=%zu results_equal=%s\n", n, ok ? "true" : "false");

  const int reps = 20;
  auto hitVal = [](Hit h) { return h ? h->second : u64{0}; };
  for (int round = 1; round <= 2; ++round) {
    std::printf("BENCH cpp round=%d\n", round);
    bench("cpp_handU", n, reps, [&](int r) { return handU(xs, r); });
    bench("cpp_viewsU", n, reps, [&](int r) { return viewsU(xs, r); });
    bench("cpp_eagerU", n, reps, [&](int r) { return eagerU(xs, r); });
    bench("cpp_provedU", n, reps, [&](int r) { return provedU(xs, r); });
    bench("cpp_handA", n, reps, [&](int r) { return handA(es, 50000 + r % 2, 90).total; });
    bench("cpp_viewsA", n, reps, [&](int r) { return viewsA(es, 50000 + r % 2, 90).total; });
    bench("cpp_eagerA", n, reps, [&](int r) { return eagerA(es, 50000 + r % 2, 90).total; });
    bench("cpp_provedA", n, reps, [&](int r) { return provedA(es, 50000 + r % 2, 90).total; });
    bench("cpp_handF_miss", n, reps, [&](int r) { return hitVal(handF(xs, big + 1 + r)); });
    bench("cpp_viewsF_miss", n, reps, [&](int r) { return hitVal(viewsF(xs, big + 1 + r)); });
    bench("cpp_eagerF_miss", n, reps, [&](int r) { return hitVal(eagerF(xs, big + 1 + r)); });
    bench("cpp_provedF_miss", n, reps, [&](int r) { return hitVal(provedF(xs, big + 1 + r)); });
  }
  return ok ? 0 : 1;
}
