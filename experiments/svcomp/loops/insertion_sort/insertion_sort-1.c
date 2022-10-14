#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "insertion_sort-1.c", 3, "reach_error"); }
#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
int main(int argc, char** argv) {
   unsigned int SIZE= atoi(argv[1]);
   //klee_make_symbolic(&SIZE, sizeof(SIZE), "size");
   int i, j, k, key,a=1;
   int v[SIZE];
   for (j=0;j<SIZE;j++)
      v[j] = SIZE-j;  
   for (j=1;j<SIZE;j++) {	  
      key = v[j];
      i = j - 1;
      while((i>=0) && (v[i]>key)) {
        if(__cpr_choice("L290", "bool", (int[]){i,a}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0))
         v[i+1] = v[i];
         i = i - 1;
      }
      v[i+1] = key;	        
  }      
  for (k=1;k<SIZE;k++){
       int diff = v[k] - v[k-1];
       CPR_OUTPUT("obs", "i32", diff);
    __VERIFIER_assert(v[k-1]<=v[k]);

   }

  if (SIZE > 0)
   printf("END");  
   return 0;
}
