int global;

void callee()
  __CPROVER_ensures(global >= 10)
{
  global = 20;
}

int main()
{
  callee();
  __CPROVER_assert(global >= 10, "property 1");
  return 0;
}
