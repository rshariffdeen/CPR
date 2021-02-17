#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = __trident_choice("L9", "i32", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0);
  TRIDENT_OUTPUT("obs", "i32", y - (x*x));
  return 0;
}
