#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define N 10

int main ( ) {
  int a[N];
  int b[N];
  int i = 0;

   klee_make_symbolic(&a, sizeof(a), "a");
	i=0;
  while ( i < N ) {
    if ( a[i] >= 0 ) b[i] = 1;
    else b[i] = 0;
    i = i + 1;
  }
  int f = 1;
  i = 0;
  while ( i < N ) {
    if ( a[i] >= 0 && !b[i] ) f = 0;
    if ( __trident_choice("L290", "i32", (int[]){a[i],b[i]}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0) ) f = 0;
    i = i + 1;
  }
  TRIDENT_OUTPUT("obs", "i32", f);
  __VERIFIER_assert ( f );
  return 0;
}