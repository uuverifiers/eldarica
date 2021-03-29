struct S {
  int f;
};

void main() {
  int *x = calloc(sizeof(int));
  struct S *y = (struct S *) x;
  int *z = y;
  assert(*z == 0);
  *x = 42;
  assert(*z == *x);
  assert(*z == 42);
}

