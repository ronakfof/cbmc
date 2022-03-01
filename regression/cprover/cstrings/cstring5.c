int main()
{
  char buffer[100], *p, ch;
  p = &ch;
  buffer[10] = 0;
  *p = 'a'; // possibly wreck, but doesn't happen
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // passes
  return 0;
}
