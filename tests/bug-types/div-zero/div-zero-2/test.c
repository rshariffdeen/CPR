#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res, z;
  if (__cpr_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (x > 5)
    z = x - 7;
  else
    z = x + 2;

  CPR_OUTPUT("obs", "i32", z);
  res = 1000 / z;
  return 0;
}








