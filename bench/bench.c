/* SIFT10K scoring harness for 5 kernels x {generated, hand-written}. modes: correct | time ROUNDS */
#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define NQ 100
#define NX 10000
#define DIM 128
#define NK 5
typedef int (*fn)(const int8_t *, const int8_t *, size_t, int32_t *);
#define DECL(k) int gen_##k(const int8_t *, const int8_t *, size_t, int32_t *); \
                int hand_##k(const int8_t *, const int8_t *, size_t, int32_t *);
DECL(dot) DECL(l1) DECL(l2) DECL(ham) DECL(osl)
static fn volatile FN[NK][2] = {{gen_dot, hand_dot}, {gen_l1, hand_l1}, {gen_l2, hand_l2}, {gen_ham, hand_ham}, {gen_osl, hand_osl}};
static const char *KN[NK] = {"dot", "l1", "l2", "ham", "osl"}, *FORM[2] = {"gen", "hand"};
static uint8_t Qu[NQ * DIM], Xu[NX * DIM];
static int8_t Q[NQ * DIM], X[NX * DIM];
static int32_t GT[NQ * 100];
static void load(const char *p, void *buf, size_t bytes) {
  FILE *f = fopen(p, "rb");
  if (!f || fread(buf, 1, bytes, f) != bytes || fgetc(f) != EOF) { fprintf(stderr, "FAIL reading %s\n", p); exit(2); }
  fclose(f);
}
static int64_t ref(int k, const int8_t *a, const int8_t *b) {   /* independent exact int64 reference */
  int64_t s = 0;
  for (int i = 0; i < DIM; i++) {
    int64_t x = a[i], y = b[i];
    switch (k) {
      case 0: s += x * y; break;
      case 1: s += x > y ? x - y : y - x; break;
      case 2: s += (x - y) * (x - y); break;
      case 3: s += x != y; break;
      default: s += x > y ? x - y : 0;
    }
  }
  return s;
}
static int64_t pass(int k, int f) {
  fn g = FN[k][f]; int64_t sum = 0; int32_t out;
  for (int q = 0; q < NQ; q++)
    for (int j = 0; j < NX; j++) { if (g(Q + q * DIM, X + j * DIM, DIM, &out) != 0) exit(4); sum += out; }
  return sum;
}
static int32_t D[NX]; static int IDX[NX];
static int cmpd(const void *p, const void *q) { int i = *(const int *)p, j = *(const int *)q; return D[i] != D[j] ? (D[i] < D[j] ? -1 : 1) : i - j; }
static int cmpi(const void *p, const void *q) { int32_t a = *(const int32_t *)p, b = *(const int32_t *)q; return (a > b) - (a < b); }
int main(int argc, char **argv) {
  if (argc < 2) return 64;
  load("work/data/q.u8", Qu, sizeof Qu); load("work/data/x.u8", Xu, sizeof Xu); load("work/data/gt.i32", GT, sizeof GT);
  for (size_t i = 0; i < sizeof Qu; i++) Q[i] = (int8_t)((int)Qu[i] - 128);
  for (size_t i = 0; i < sizeof Xu; i++) X[i] = (int8_t)((int)Xu[i] - 128);
  int64_t ck[NK];
  for (int k = 0; k < NK; k++) {                 /* correctness pass (untimed) */
    long mm = 0; int64_t s = 0; int32_t o0, o1;
    for (int q = 0; q < NQ; q++) for (int j = 0; j < NX; j++) {
      const int8_t *a = Q + q * DIM, *b = X + j * DIM; int64_t r = ref(k, a, b);
      if (FN[k][0](a, b, DIM, &o0) || FN[k][1](a, b, DIM, &o1) || o0 != r || o1 != r) mm++;
      s += r;
    }
    ck[k] = s;
    if (!strcmp(argv[1], "correct")) printf("correct %s: pairs=%d mismatches(gen|hand vs int64 ref)=%ld checksum=%lld\n", KN[k], NQ * NX, mm, (long long)s);
    if (mm) { printf("FAIL %s mismatches\n", KN[k]); return 3; }
  }
  if (!strcmp(argv[1], "correct")) {            /* squared L2 vs published Euclidean neighbours */
    int t1 = 0, t10 = 0, t100 = 0, ord100 = 0;
    for (int q = 0; q < NQ; q++) {
      for (int j = 0; j < NX; j++) { int32_t o; FN[2][0](Q + q * DIM, X + j * DIM, DIM, &o); D[j] = o; IDX[j] = j; }
      qsort(IDX, NX, sizeof(int), cmpd);
      int e1 = IDX[0] == GT[q * 100], e10 = 1, eo = 1;
      for (int r = 0; r < 10; r++) e10 &= IDX[r] == GT[q * 100 + r];
      for (int r = 0; r < 100; r++) eo &= IDX[r] == GT[q * 100 + r];
      int32_t a[100], b[100];
      for (int r = 0; r < 100; r++) { a[r] = D[IDX[r]]; b[r] = D[GT[q * 100 + r]]; }
      qsort(b, 100, sizeof(int32_t), cmpi);
      t1 += e1; t10 += e10; ord100 += eo; t100 += !memcmp(a, b, sizeof a);
    }
    printf("l2 vs published: top1 ordered %d/100, top10 ordered %d/100, top100 tie-aware distances %d/100, top100 identical ordered ids (index tie-break) %d/100\n", t1, t10, t100, ord100);
    return (t1 == 100 && t10 == 100 && t100 == 100) ? 0 : 5;
  }
  int R = atoi(argv[2]); if (R < 1 || R > 1000) return 64;
  for (int c = 0; c < 2 * NK; c++) if (pass(c / 2, c % 2) != ck[c / 2]) return 3;   /* warm-up */
  printf("round,kernel,form,ms\n");
  for (int r = 0; r < R; r++)
    for (int i = 0; i < 2 * NK; i++) {
      int c = (i + r) % (2 * NK), k = c / 2, f = c % 2;
      struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
      int64_t s = pass(k, f);
      clock_gettime(CLOCK_MONOTONIC, &t1);
      if (s != ck[k]) { fprintf(stderr, "FAIL checksum %s %s\n", KN[k], FORM[f]); return 3; }
      printf("%d,%s,%s,%.4f\n", r, KN[k], FORM[f], (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6);
    }
  return 0;
}
