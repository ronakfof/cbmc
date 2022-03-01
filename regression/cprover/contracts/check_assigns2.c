struct some_struct
{
  int field;
};

void my_function1(int parameter) __CPROVER_assigns() // passes
{
  parameter = 1;
}

void my_function2(void) __CPROVER_assigns() // passes
{
  struct some_struct s;
  s.field = 1;

  int array[123];
  array[1] = 2;
}
