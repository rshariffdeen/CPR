#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int varA = atoi(argv[1]);
  int varB = atoi(argv[2]);
  int varC;
  int res;
  if (__cpr_choice("L9", "bool", (int[]){varA, varB}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))  {
      return -1;
  }

  if (varA > 0)
    varC = varB * varA;
  else
    varC = 2;
  CPR_OUTPUT("obs", "i32", varC);
  res = 200/varC;
  return 0;
}
