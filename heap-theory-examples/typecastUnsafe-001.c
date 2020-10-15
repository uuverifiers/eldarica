struct S {
  int f;
};

void main() {
  int *x = calloc(sizeof(int));
  struct S *y = (struct S *) x;
  y->f = 42;
  assert(y->f == 42);
}

