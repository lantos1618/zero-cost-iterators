// Result chains: the same validation written three ways, checked equal, then timed.
//   hand: early-return code;  expected: a Result type's and_then (like std::expected), flat and nested;
//   ours: provedCheck, printed from Iter.Res.check (Iter.Res.checkChain_gen).
#include "common.hpp"

// A library Result type with and_then, as std::expected (C++23; GCC 13+, so not in GCC 12's or clang 15's
// standard library here) and tl::expected implement it: every step returns a Result, and_then inspects it.
struct Ex {
  bool has; u64 v;
  Ex(u64 x) : has(true), v(x) {}
  static Ex fail(u64 e) { Ex r(e); r.has = false; return r; }
  explicit operator bool() const { return has; }
  u64 operator*() const { return v; }
  u64 error() const { return v; }
  template <class F> Ex and_then(F f) const { return has ? f(v) : *this; }
};
// the same tests as the Lean chain, written as early returns
NOINLINE Res handCheck(u64 x, u64 k) {
  if (!(x < 1000000000000ULL)) return {0, 1};
  x = x * 10 + k;
  if (!(x % 7 < 6)) return {0, 2};
  x ^= 0x5bd1e995;
  if (!(x % 97 < 96)) return {0, 3};
  return {1, x};
}

// equal results, but `x % 7 == 6` instead of `!(x % 7 < 6)`: clang then uses a multiply-compare
// divisibility test instead of a full remainder. A difference in how the test is spelled, not in the chain.
NOINLINE Res handEq(u64 x, u64 k) {
  if (x >= 1000000000000ULL) return {0, 1};
  x = x * 10 + k;
  if (x % 7 == 6) return {0, 2};
  x ^= 0x5bd1e995;
  if (x % 97 == 96) return {0, 3};
  return {1, x};
}

static Ex s1(u64 x) { if (x < 1000000000000ULL) return x; return Ex::fail(1ULL); }
static Ex s3(u64 x) { if (x % 7 < 6) return x; return Ex::fail(2ULL); }
static Ex s4(u64 x) { return x ^ 0x5bd1e995; }
static Ex s5(u64 x) { if (x % 97 < 96) return x; return Ex::fail(3ULL); }
static Res toRes(const Ex& r) { return r ? Res{1, *r} : Res{0, r.error()}; }

NOINLINE Res expFlat(u64 x, u64 k) {
  return toRes(Ex(x).and_then(s1).and_then([k](u64 y) -> Ex { return y * 10 + k; })
                 .and_then(s3).and_then(s4).and_then(s5));
}

// the nesting of Iter.Res.check: ((s1 >=> s2) >=> (s3 >=> (s4 >=> s5)))
NOINLINE Res expNested(u64 x, u64 k) {
  return toRes(Ex(x).and_then([k](u64 a) { return s1(a).and_then([k](u64 y) -> Ex { return y * 10 + k; }); })
                 .and_then([](u64 b) { return s3(b).and_then([](u64 c) { return s4(c).and_then(s5); }); }));
}

int main(int argc, char**) {
  constexpr std::size_t n = 1 << 20;
  std::vector<u64> xs(n);
  for (u64 t = 3; u64& x : xs) {
    t = t * 6364136223846793005ULL + 1442695040888963407ULL;
    x = (t >> 20) % 1100000000000ULL;  // about 9% fail the first check
  }
  using F = Res (*)(u64, u64);
  const std::vector<std::pair<const char*, F>> fs = {{"hand", &handCheck}, {"hand_eq", &handEq},
      {"expected_flat", &expFlat}, {"expected_nested", &expNested},
      {"ours", &provedCheck}};
  u64 bad = 0, errs[4] = {0, 0, 0, 0};
  for (u64 k : {0ULL, 7ULL, 12345ULL})
    for (u64 x : xs) {
      Res h = handCheck(x, k);
      if (h.ok == 0) ++errs[h.val];
      for (auto& [nm, f] : fs) { Res r = f(x, k); bad += r.ok != h.ok || r.val != h.val; }
    }
  std::printf("CHAIN results_equal=%s errors: e1=%llu e2=%llu e3=%llu of %zu\n", bad ? "NO" : "yes",
              (unsigned long long)errs[1], (unsigned long long)errs[2], (unsigned long long)errs[3], 3 * n);
  if (argc > 1) return bad != 0;  // check only
  for (auto& [nm, f] : fs) {
    std::string label = std::string("chain/") + nm;
    bench(label.c_str(), n, 3, [&, f = f](int r) {
      u64 a = 0;
      for (u64 x : xs) { Res v = f(x, (u64)r); a += v.ok ? v.val : v.val * 31; }
      return a;
    });
  }
  return bad != 0;
}
