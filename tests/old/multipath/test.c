#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  while (__cpr_choice("L10", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0)) {
    x++;
  }
  return CPR_OUTPUT("x", "i32", x);
}
