#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = atoi(argv[2]);
  int b;
  int res;
  if (__cpr_choice("L12", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (__cpr_choice("L16", "bool", (int[]){y}, (char*[]){"y"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (x > 0)
    b = y * x;
  else
    b = 2;
  CPR_OUTPUT("obs", "i32", b);
  res = 200/b;
  return 0;
}
