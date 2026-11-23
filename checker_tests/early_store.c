/* emitted by gen.py from ir/pos.json -- do not edit */
#include <stddef.h>
#include <stdint.h>
#define I8DOT_MAX_N 131071u

int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {
  if (n > I8DOT_MAX_N) return -1;
  int32_t acc = 0;
  int32_t r0 = 0;
  int32_t r1 = 0;
  *out = acc;
  for (size_t i = 0; i < n; i++) {
    r0 = (int32_t)a[i];
    r1 = (int32_t)b[i];
    r0 = r0 * r1;
    acc = acc + r0;
  }
  return 0;
}
