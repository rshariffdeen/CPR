#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = __cpr_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0);
  int res;
  if (y)  {
      printf("PATH ONE");
      res = x + 1;
  } else {
      printf("PATH TWO");
      res = x - 1;
  }
  return CPR_OUTPUT("res", "i32", res);
}
