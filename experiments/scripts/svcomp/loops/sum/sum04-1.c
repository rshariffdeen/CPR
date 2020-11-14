#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main() {
  int i, sn=0;
  int a, size;
  klee_make_symbolic(&a, sizeof(int), "a");
  klee_make_symbolic(&size, sizeof(int), "size");
  a = 2;
  size = 8;
  for(i=1; i<=size; i++) {
    if (__trident_choice("L9", "bool", (int[]){i, sn}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))
    sn = sn + a;
  }
  TRIDENT_OUTPUT("obs", "i32", sn==size*a || sn == 0);
  __VERIFIER_assert(sn==size*a || sn == 0);
}