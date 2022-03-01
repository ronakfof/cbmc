int main()
{
  char buffer[100], ch;
  buffer[10] = 0;
  ch = 'a'; // does not affect 'buffer'
  __CPROVER_assert(__CPROVER_is_cstring(buffer), "property 1"); // passes
  return 0;
}
