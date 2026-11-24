// Shared by bench.cpp and falsify.cpp: data types, the plain and branch-free hand loops, the generated
// proved loops, the workloads, the timer and the tuner. No <ranges>, so it builds with any C++20 compiler.
#pragma once
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#define NOINLINE __attribute__((noinline))
using u64 = std::uint64_t;

struct Emp { std::string_view name; u64 salary; bool active; };
struct Summ { u64 count = 0, total = 0; std::string_view first, last; };
using Hit = std::optional<std::pair<std::size_t, u64>>;

static Summ summStep(Summ s, std::string_view name, u64 pay) {
  if (s.count == 0) s.first = name;
  s.count += 1; s.total += pay; s.last = name;
  return s;
}
NOINLINE u64 handU(const std::vector<u64>& xs, u64 k) {
  u64 acc = 0;
  for (u64 x : xs) if ((x ^ k) % 3 == 0) acc += x * 2;
  return acc;
}
NOINLINE u64 handC(const std::vector<u64>& xs, u64 k) {
  u64 c = 0;
  for (u64 x : xs) if ((x ^ k) % 3 == 0) ++c;
  return c;
}
NOINLINE std::optional<u64> handMax(const std::vector<u64>& xs, u64 k) {
  std::optional<u64> m;
  for (u64 x : xs) if ((x ^ k) % 3 == 0) { u64 y = x * 2; if (!m || y > *m) m = y; }
  return m;
}
NOINLINE Summ handA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  Summ s;
  for (const Emp& e : es) if (e.active && e.salary >= minSal) s = summStep(s, e.name, e.salary * pct / 100);
  return s;
}
NOINLINE Hit handF(const std::vector<u64>& xs, u64 t) {
  for (std::size_t i = 0; i < xs.size(); ++i) if (xs[i] > t) return std::pair{i, xs[i]};
  return std::nullopt;
}

// Branch-free hand loops: what a C++ programmer who knows the mask trick writes in a few minutes.
// They are the strongest baseline here; falsify.sh checks ours against them.
NOINLINE u64 bfU(const std::vector<u64>& xs, u64 k) {
  u64 acc = 0;
  for (u64 x : xs) acc += (x * 2) & (0 - (u64)((x ^ k) % 3 == 0));
  return acc;
}
NOINLINE u64 bfC(const std::vector<u64>& xs, u64 k) {
  u64 c = 0;
  for (u64 x : xs) c += (x ^ k) % 3 == 0;
  return c;
}
NOINLINE std::optional<u64> bfMax(const std::vector<u64>& xs, u64 k) {
  u64 m = 0, seen = 0;
  for (u64 x : xs) { u64 kb = (x ^ k) % 3 == 0; seen |= kb; m = std::max(m, (x * 2) & (0 - kb)); }
  return seen ? std::optional<u64>(m) : std::nullopt;
}
NOINLINE Summ bfA(const std::vector<Emp>& es, u64 minSal, u64 pct) {
  u64 cnt = 0, tot = 0;
  const Emp *fp = nullptr, *lp = nullptr;
  for (const Emp& e : es) {
    u64 kb = (u64)e.active & (u64)(e.salary >= minSal);
    cnt += kb; tot += (e.salary * pct / 100) & (0 - kb);
    fp = !fp && kb ? &e : fp; lp = kb ? &e : lp;
  }
  Summ s; s.count = cnt; s.total = tot;
  if (fp) { s.first = fp->name; s.last = lp->name; }
  return s;
}

// Proved rewrites. provedU, provedC, provedMax, provedA and adaptA are generated from Lean (gen/proved_gen.hpp, proved by
// Iter.Gen.wordPipe_gen and Iter.Gen.recPipe_gen; the printer is trusted). provedF below is written by hand
// from Iter.Rewrite.chain_find_blocks and checked only by the results_equal test.
#include "gen/proved_gen.hpp"

NOINLINE Hit findBlocks(const std::vector<u64>& xs, u64 t) {
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

NOINLINE Hit findPlain(const std::vector<u64>& xs, u64 t) {
  for (std::size_t i = 0; i < xs.size(); ++i) if (xs[i] > t) return std::pair{i, xs[i]};
  return std::nullopt;
}
struct FindCand { const char* tag; Hit (*f)(const std::vector<u64>&, u64); };
static const FindCand provedF_cands[] = {{"plain", &findPlain}, {"blocks", &findBlocks}};

// the loops "ours" runs: picked by tune() below from candidates that all compute the same result
static u64 (*provedU)(const std::vector<u64>&, u64);
static u64 (*provedC)(const std::vector<u64>&, u64);
static Hit (*provedF)(const std::vector<u64>&, u64);

// same rows, inactive first, then by salary: the hand loop's branch becomes predictable
static std::vector<Emp> sortedRows(std::vector<Emp> es) {
  std::sort(es.begin(), es.end(), [](const Emp& a, const Emp& b) { return a.active != b.active ? a.active < b.active : a.salary < b.salary; });
  return es;
}

// same names, rows in runs of 256 that are all kept (60%) or all dropped (inactive), spread through the array:
// the hand and views loops' branch is predictable, but the dropped rows are not all at the front
static std::vector<Emp> runRows(std::vector<Emp> es, const std::vector<u64>& xs) {
  for (std::size_t i = 0; i < es.size(); ++i) {
    bool keep = (xs[(i / 256) * 256] >> 7) % 5 < 3;
    es[i].active = keep;
    es[i].salary = keep ? 50001 + xs[i] % 149999 : xs[i] % 200000;
  }
  return es;
}

// alternating 65,536-row stretches of random rows and of runs: the best loop changes inside one input
static std::vector<Emp> mixedRows(const std::vector<Emp>& rnd, const std::vector<Emp>& runs) {
  std::vector<Emp> es = rnd;
  for (std::size_t i = 0; i < es.size(); ++i) if ((i >> 16) & 1) es[i] = runs[i];
  return es;
}

template <class F>
static void bench(const char* label, std::size_t n, int reps, F f) {
  volatile u64 warm = f(0); (void)warm;
  std::vector<long long> ts;
  u64 chk = 0;
  for (int b = 0; b < 11; ++b) {
    auto t0 = std::chrono::steady_clock::now();
    u64 acc = 0;
    for (int r = 0; r < reps; ++r) acc += f(r);
    auto t1 = std::chrono::steady_clock::now();
    ts.push_back(std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count());
    chk = acc;
  }
  std::sort(ts.begin(), ts.end());
  auto per = [&](long long t) { return t * 100 / (long long)(n * reps); };
  std::printf("BENCH %s median_ns_per_item_x100=%lld min=%lld max=%lld checksum=%llu\n", label, per(ts[5]),
              per(ts.front()), per(ts.back()), (unsigned long long)chk);
}

// times every candidate on a separate sample (median of 9) and returns the fastest; this changes speed only,
// because every candidate is proved (or, for provedF, checked below) to give the same result
template <class C, std::size_t N, class R>
static decltype(C::f) tune(const char* what, const C (&cs)[N], R run) {
  std::size_t best = 0;
  long long bt = -1;
  volatile u64 sink = 0;
  for (std::size_t c = 0; c < N; ++c) {
    std::vector<long long> ts;
    for (int b = 0; b < 9; ++b) {
      auto t0 = std::chrono::steady_clock::now();
      sink = sink + run(cs[c].f);
      ts.push_back(std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - t0).count());
    }
    std::sort(ts.begin(), ts.end());
    if (bt < 0 || ts[4] < bt) { bt = ts[4]; best = c; }
  }
  std::printf("TUNE %s=%s\n", what, cs[best].tag);
  return cs[best].f;
}

// the timed workloads, and a tuning sample (same size and generator, different seed) that is never timed
struct Data { std::vector<u64> xs; std::vector<Emp> es, sorted, runs, mixed; u64 big; std::vector<u64> tx; u64 tbig; };

static Data makeData(std::size_t n) {
  Data d;
  d.xs.reserve(n);
  u64 s = 42;
  for (std::size_t i = 0; i < n; ++i) { s = s * 6364136223846793005ULL + 1442695040888963407ULL; d.xs.push_back(s >> 40); }
  static const std::string_view names[] = {"ana", "bo", "cy", "di", "ed", "flo", "gus", "hal"};
  d.es.resize(n);
  for (std::size_t i = 0; i < n; ++i) d.es[i] = {names[i % 8], d.xs[i] % 200000, d.xs[i] % 5 != 0};
  d.sorted = sortedRows(d.es);
  d.runs = runRows(d.es, d.xs);
  d.mixed = mixedRows(d.es, d.runs);
  d.big = *std::max_element(d.xs.begin(), d.xs.end());
  d.tx.resize(n);
  for (u64 t = 7; u64& x : d.tx) { t = t * 6364136223846793005ULL + 1442695040888963407ULL; x = t >> 40; }
  d.tbig = *std::max_element(d.tx.begin(), d.tx.end());
  return d;
}

static void tuneAll(const Data& d) {
  auto words = [&](auto f) { u64 a = 0; for (u64 r = 0; r < 4; ++r) a += f(d.tx, r); return a; };
  provedU = tune("provedU", provedU_cands, words);
  provedC = tune("provedC", provedC_cands, words);
  provedF = tune("provedF", provedF_cands, [&](auto f) { u64 a = 0; for (u64 r = 0; r < 4; ++r) a += f(d.tx, d.tbig + 1 + r) ? 1 : 0; return a; });
}
