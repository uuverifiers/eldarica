#include <assert.h>



int main() {
  {
    int x = 'a';
    int y = 'b';
    int z = 123U;
    assert(x + 1 == y);
    assert(z > 0);
  }

  {
    long x = 123L;
    int y = 123U;
    int z = x + 1;
    assert(x == y);
    assert(z > 0);
  }

  {
    unsigned x;
    unsigned int y;
    assert(x + y + 1 > 0);
  }

  {
    unsigned int x = 4294967040;
    assert(x > 0);
  }

  {
    long x = 5;
    assert((unsigned int)x > 0);
  }

  return 0;
}
