#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  __trident_choice("L9", "i32", (int[]){x}, (char*[]){"x"}, 1, (int*[]){&x}, (char*[]){"x"}, 1);
  return TRIDENT_OUTPUT("x", "i32", x);
}
