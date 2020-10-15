void main() {
  int *x = calloc(sizeof(int));
  int **y = 0;
  *y = x; // y is not allocated
}

