#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int res, y;
  if (__cpr_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  y = x - 1;

  CPR_OUTPUT("obs", "i32", y);
  res = 1000 / y;
  return 0;
}
