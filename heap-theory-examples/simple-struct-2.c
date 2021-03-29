typedef struct {
  int x;
  struct {
    int z;
  }y;
} S;

void main(){
  S *p = calloc(sizeof(S)); 

  p->y.z = 42;

  int v = p->y.z;
  assert(v == 0 || v == 42);

}
