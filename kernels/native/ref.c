/* Independent reference (hand-written, not emitted): exact sum in 64-bit, index k, no IR. */
#include <stddef.h>
#include <stdint.h>
long long ref_dot(const int8_t *a, const int8_t *b, size_t n) {
  long long s = 0;
  for (size_t k = 0; k < n; ++k) s += (long long)a[k] * (long long)b[k];
  return s;
}
