#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int varA = atoi(argv[1]);
  int varB = atoi(argv[2]);
  int res, z;
  if (__cpr_choice("L9", "bool", (int[]){varA, varB}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (varA > 5)
    z = varA - 1;
  else
    z = varA + 2;

  z = varA * varB;
  CPR_OUTPUT("obs", "i32", z);
  res = 1000 / z;
  return 0;
}








