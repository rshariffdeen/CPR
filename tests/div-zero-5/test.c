#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = 1;

  while (x > 0){
    x = x - 1;
    if (__trident_choice("L9", "bool", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))
      break;
    TRIDENT_OUTPUT("obs", "i32", x);
    res = 1000 / x;
  }

  return 0;
}








