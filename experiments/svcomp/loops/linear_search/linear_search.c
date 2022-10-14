#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "linear_search.c", 3, "reach_error"); }
void *malloc(unsigned int size);

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
unsigned int __VERIFIER_nondet_uint();
unsigned int  SIZE;
const unsigned int MAX = 100000;
int linear_search(int *a, int n, int q) {
  unsigned int j=0;
  int constant = -1;
  while (j<n && a[j]!=q) {
    j++;
    if(__cpr_choice("L290", "bool", (int[]){j,constant}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) j=-1;
  }
  if (j<SIZE) return 1;
  else return 0;
}
int main(int argc, char** argv) {
  int x = atoi(argv[1]);
  int y = atoi(argv[2]);
  SIZE=(x/2)+1;

  if (SIZE > 1 && SIZE < MAX) {
     int *a = malloc(sizeof(int)*SIZE);
    a[SIZE/2]=y;
    int ret = linear_search(a,SIZE,y);
     CPR_OUTPUT("obs", "i32", ret);
    __VERIFIER_assert(ret);
  }
}

