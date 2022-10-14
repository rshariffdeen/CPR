#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

//#define N 10

int main(int argc, char** argv) {
  unsigned int N= atoi(argv[1]);
  int a[ N ];
	for(int j = 0; j < N; j++)
	{
	  a[j] = N-j;
	}

  int swapped = 1;
  while ( swapped ) {
    swapped = 0;
    int i = 1;
    while ( i < N ) {
      if(__cpr_choice("L290", "bool", (int[]){a[i - 1],a[i]}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)){
        int t = a[i];
        a[i] = a[i - 1];
        a[i-1] = t;
        swapped = 1;
      }
      i = i + 1;
    }
  }

  int x;
  int y;
  for ( x = 0 ; x < N ; x++ ) {
    for ( y = x+1 ; y < N ; y++ ) {
       CPR_OUTPUT("obs", "i32", a[y] - a[x]);
      __VERIFIER_assert(  a[x] <= a[y]  );
    }
  }
  return 0;
}