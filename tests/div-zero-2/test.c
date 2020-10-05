#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res, z;
  if (__trident_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (x > 5)
    z = x - 1;
  else
    z = x + 2;

  TRIDENT_OUTPUT("obs", "i32", z);
  res = 1000 / z;
  return 0;
}








