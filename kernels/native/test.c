/* finite native differential test: one emitted kernel (linked as i8dot) vs independent int64 references */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out);
static int64_t ref(int k, const int8_t *a, const int8_t *b, size_t n) {
  int64_t s = 0;
  for (size_t i = 0; i < n; i++) {
    int64_t x = a[i], y = b[i], d = x - y;
    s += k == 0 ? x * y : k == 1 ? (d < 0 ? -d : d) : k == 2 ? d * d : k == 3 ? (x != y) : (d > 0 ? d : 0);
  }
  return s;
}
static uint64_t st = 0x9E3779B97F4A7C15ull;
static int8_t rnd8(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return (int8_t)(st & 0xFF); }
static int fails = 0, runs = 0, skipped = 0;
static size_t L;  /* readable length of a and b */
static void chk(int k, size_t N, const int8_t *a, const int8_t *b, size_t n, const char *tag) {
  if (n <= N && n > L) { skipped++; return; }  /* in-range but longer than the allocated arrays: not run */
  int32_t out = 0x5A5A5A5A; int r = i8dot(a, b, n, &out); runs++;
  if (n > N) { if (r != -1 || out != 0x5A5A5A5A) { fails++; printf("FAIL %s n=%zu: over-limit r=%d out=%d\n", tag, n, r, out); } return; }
  int64_t e = ref(k, a, b, n);
  if (r != 0 || (int64_t)out != e) { fails++; printf("FAIL %s n=%zu r=%d out=%d ref=%lld\n", tag, n, r, out, (long long)e); }
}
int main(int argc, char **argv) {
  if (argc != 3 && argc != 4) return 64;
  int k = atoi(argv[1]); size_t N = (size_t)strtoull(argv[2], 0, 10);
  L = N + 2; if (argc == 4 && (size_t)strtoull(argv[3], 0, 10) < L) L = (size_t)strtoull(argv[3], 0, 10);  /* optional memory cap */
  int8_t *a = malloc(L), *b = malloc(L);
  if (!a || !b) { printf("FAIL malloc %zu\n", L); return 2; }
  int8_t ext[2] = {-128, 127};
  for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) {        /* constant extreme arrays at the guard */
    memset(a, ext[i], L); memset(b, ext[j], L);
    size_t ns[] = {0, 1, 2, N - 1, N, N + 1, N + 2};
    for (int q = 0; q < 7; q++) chk(k, N, a, b, ns[q], "extreme");
  }
  for (size_t i = 0; i < L; i++) { a[i] = rnd8(); b[i] = rnd8(); }   /* deterministic xorshift data */
  size_t ns[] = {0, 1, 2, 3, 7, 8, 15, 16, 31, 64, 127, 128, 1000, 4097, N - 1, N, N + 1};
  for (int q = 0; q < 17; q++) chk(k, N, a, b, ns[q], "random");
  for (int t = 0; t < 2000; t++) {                                  /* random lengths, random offsets */
    size_t n = (size_t)(rnd8() & 0x7F) * 7 + (size_t)(rnd8() & 7), off = (size_t)(rnd8() & 0x3F);
    if (off + n <= L) chk(k, N, a + off, b + off, n, "random-len");
  }
  int64_t worst = ref(k, ext + (k == 0 ? 0 : 1), ext, 1) * (int64_t)N;
  printf("kernel=%d N=%zu readable=%zu runs=%d skipped=%d fails=%d worst_case_N_sum=%lld (INT32_MAX=2147483647)\n", k, N, L, runs, skipped, fails, (long long)worst);
  return fails != 0;
}
