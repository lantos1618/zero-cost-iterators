/* emitted by gen.py from ir/ham_buf.json -- do not edit */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#define I8DOT_MAX_N 2147483647u

int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {
  if (n > I8DOT_MAX_N) return -1;
  int32_t acc = 0;
  int32_t r0 = 0;
  int32_t r1 = 0;
  int32_t *t = (int32_t *)malloc((n ? n : 1) * sizeof(int32_t));
  if (!t) return -2;
  for (size_t i = 0; i < n; i++) {
    r0 = (int32_t)a[i];
    r1 = (int32_t)b[i];
    r0 = r0 - r1;
    r0 = r0 != 0;
    t[i] = r0;
  }
  for (size_t i = 0; i < n; i++) {
    r0 = t[i];
    acc = acc + r0;
  }
  free(t);
  *out = acc;
  return 0;
}
