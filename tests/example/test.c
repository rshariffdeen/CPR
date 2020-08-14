#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  klee_print_expr("x", x);
  int y = __trident_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0);
  int res;
  if (y)  {
      res = 1;
  } else {
      res = 0;
  }
  return TRIDENT_OUTPUT("res", "i32", res);
}
