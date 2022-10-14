#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

#define INVALID -1
#define EQUILATERAL 0
#define ISOSCELES 1
#define SCALENE 2

int main(int argc, char *argv[]) {
  int a = atoi(argv[1]);
  int b = atoi(argv[2]);
  int c = atoi(argv[3]);

  if ( a <=0 || b <= 0 || c <= 0)
        return INVALID;
  if ( a == b && b== c )
        return EQUILATERAL;
  if ( a== b || __cpr_choice("L9", "bool", (int[]){a,b,c}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0))
        return ISOSCELES;

  int obs = (a-b) * (b-c) * (c - a);
  CPR_OUTPUT("obs", "i32", obs);
  return SCALENE;
}
