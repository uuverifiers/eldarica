struct simple{
  int x;
};

void main(){
  struct simple *p = calloc(sizeof(struct simple));
  p->x = 42;
  int v = p->x;
  assert(v == 42 || v ==0);
}
