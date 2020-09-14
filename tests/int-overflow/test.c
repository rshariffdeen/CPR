#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = atoi(argv[2]);
  int a = 214748364 ;
  int b;
  int res;
  if (__trident_choice("L9", "bool", (int[]){x, y}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }
  b = y * a;
  TRIDENT_OUTPUT("b", "i32", b);
  res = x * b;
  return 0;
}
