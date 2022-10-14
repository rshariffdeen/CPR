#include <stdio.h>
#include <limits.h>
#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int a = 214748364 ;
  int b;
  if (__cpr_choice("L9", "bool", (int[]){x, a, INT_MAX}, (char*[]){"x", "a", "y"}, 3, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }
  CPR_OUTPUT("obs", "i32", (INT_MAX/a) - x);
  b = x * a;
  return 0;
}
