#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

#define MAX 5

extern char __VERIFIER_nondet_char();

int main()
{
  char string_A[MAX], string_B[MAX];
  int i, j, nc_A, nc_B, found=0;

  for(i=0; i<MAX; i++){
    string_A[i]="x";
    string_A[i]="y";
  }
  klee_make_symbolic(&string_A, sizeof(string_A), "A");
  if (!(string_A[MAX-1]=='\0')) return 0;
  klee_make_symbolic(&string_B, sizeof(string_B), "B");


  if (!(string_B[MAX-1]=='\0')) return 0;

  nc_A = 0;
  while(string_A[nc_A]!='\0')
    nc_A++;

  nc_B = 0;
  while(string_B[nc_B]!='\0')
    nc_B++;

  if (!(nc_B >= nc_A)) return 0;


  i=j=0;
  while((i<nc_A) && (j<nc_B))
  {
    if(string_A[i] == string_B[j])
    {
       i++;
       j++;
    }
    else
    {
       i = i-j+1;
       j = 0;
    }
  }
  int res = (j>nc_B-1);
//  found = (j>nc_B-1)<<i;
  found = __cpr_choice("L9", "i32", (int[]){res, i}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0);
  CPR_OUTPUT("obs", "i32", found);
  __VERIFIER_assert(found == 0 || found == 1);

  return 0;
}