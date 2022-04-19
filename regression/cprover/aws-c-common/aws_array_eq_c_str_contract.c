// Function: aws_array_eq_c_str

#include <aws/common/byte_buf.h>

// bool aws_array_eq_c_str_ignore_case(const void *const array, const size_t array_len, const char *const c_str)

int main()
{
  const void *array;
  size_t array_len;
  const char *c_str;

  __CPROVER_assume(__CPROVER_r_ok(array, array_len));
  __CPROVER_assume(__CPROVER_is_cstring(c_str));

  aws_array_eq_c_str_ignore_case(array, array_len, c_str);

  return 0;
}
