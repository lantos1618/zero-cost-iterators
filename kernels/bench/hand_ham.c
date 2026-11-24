#include <stddef.h>
#include <stdint.h>
int hand_ham(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {
  if (n > 2147483647u) return -1;
  int32_t acc = 0;
  for (size_t i = 0; i < n; i++) acc += a[i] != b[i];
  *out = acc;
  return 0;
}
