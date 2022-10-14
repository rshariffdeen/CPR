#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int a = atoi(argv[1]);
  int x = 1;
  int y = 1;

  int res, z;
  if (a > 5)
    y = y - 1;

  else
    x = x -1;


  if (__cpr_choice("L9", "bool", (int[]){x, y}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  z = x * y;
  CPR_OUTPUT("obs", "i32", z);
  res = 1000 / z;
  return 0;
}








