int main()
{
  const char *p;

  __CPROVER_assume(__CPROVER_is_cstring(p));

  __CPROVER_size_t i = 0;

  while(p[i] != 0)
    __CPROVER_loop_invariant(__CPROVER_is_cstring(p) && i>=0 && i<=__CPROVER_cstrlen(p))
  {
    i++;
  }

  return 0;
}
