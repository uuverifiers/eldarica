unsigned int __VERIFIER_nondet_uint(void);
int main(void) {
  unsigned int x = 0;
  unsigned int y = __VERIFIER_nondet_uint();
  while (x < 9) {
    if (y % 2 == 0) {
      x += 2;
    } else {
      x++;
    }
  }
  __VERIFIER_assert((x % 2) == (y % 2));
}
