#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = 1;

  int res, z;
  if (x > 5)
    y = y - 1;
  else
    y = y + 2;


  if (__cpr_choice("L9", "bool", (int[]){x, y}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  z = x * y;
  CPR_OUTPUT("obs", "i32", z);
  res = 1000 / z;
  return 0;
}








