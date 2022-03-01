void *malloc(__CPROVER_size_t);

int main()
{
  int n;
  __CPROVER_assume(n >= 0);
  int *array = malloc(sizeof(int) * n);

  for(int i = 0; i != n; i++)
    __CPROVER_loop_invariant(
      i >= 0 && i <= n &&
      __CPROVER_OBJECT_SIZE(array) == sizeof(int) * n) // passes
  {
    array[i] = 0; // safe and passes
  }

  return 0;
}
