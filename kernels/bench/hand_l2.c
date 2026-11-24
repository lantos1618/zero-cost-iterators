#include <stddef.h>
#include <stdint.h>
int hand_l2(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {
  if (n > 33025u) return -1;
  int32_t acc = 0;
  for (size_t i = 0; i < n; i++) {
    int32_t d = (int32_t)a[i] - b[i];
    acc += d * d;
  }
  *out = acc;
  return 0;
}
