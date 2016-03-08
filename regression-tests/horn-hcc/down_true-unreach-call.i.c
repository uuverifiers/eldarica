extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();
int main() {
  int n;
  int k = 0;
  int /*@ predicates { k >= i } @*/ i = 0;
  n = __VERIFIER_nondet_int();
  while( i < n ) {
      i++;
      k++;
  }
  int  /*@ predicates { k >= j } @*/ j = n;
  while( j > 0 ) {
      __VERIFIER_assert(k > 0);
      j--;
      k--;
  }
  return 0;
}
