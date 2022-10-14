#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  for (int i=0; i<3; i++)
    __cpr_choice("L10", "i32", (int[]){x}, (char*[]){"x"}, 1, (int*[]){&x}, (char*[]){"x"}, 1);
  return CPR_OUTPUT("x", "i32", x);
}
