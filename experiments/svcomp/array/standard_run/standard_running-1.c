#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();



int main (int argc, char** argv) {
 unsigned int N= atoi(argv[1]);
  int a[N];
  int b[N];
  int i = 0;
  for (i=0;i<N;i++)
      a[i] = N-i-3;
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
    if ( a[i] < 0 && __cpr_choice("L290", "bool", (int[]){a[i],b[i]}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0) ) f = 0;
    i = i + 1;
  }
  CPR_OUTPUT("obs", "i32", f);
  __VERIFIER_assert ( f );
  return 0;
}