#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int z = atoi(argv[2]);
  int res, y;
  if (__trident_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (z > 10)
    y = x - 1;
  else
    y = x + 2;

  TRIDENT_OUTPUT("y", "i32", y);
  res = z / y;
  return 0;
}
