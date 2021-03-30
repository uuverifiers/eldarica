
void main() {
    int *x = calloc(sizeof(int));
    *x = 42;
    *x = 3;
    int y = *x + *x;
    assert(y == 0 || y == 3 || y == 6 || y == 42 || y == 45 || y == 84);
    /* possible values for y using the invariant encoding without refinements
      0  +  0 = 0
      0  +  3 = 3
      3  +  3 = 6
      0  + 42 = 42
      3  + 42 = 45
      42 + 42 = 84

      with refinements
      3 + 3 = 6
      */
}

