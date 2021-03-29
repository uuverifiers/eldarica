struct S {
  int x;
} *s;

void main() {
  s = calloc(sizeof(struct S));
  s->x += 42;
  assert(s->x == 42);
  s->x *= 2;
  assert(s->x == 84);
  s->x /= 4;
  assert(s->x == 21);
  s->x -= 1;
  assert(s->x == 20);
  s->x %= 3;
  assert(s->x == 2);
  s->x -= s->x;
  assert(s->x == 0);
}

