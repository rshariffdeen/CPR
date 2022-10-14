#include <klee/klee.h>
#include<stdio.h>
#include<stdint.h>
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Addition02.c", 3, "reach_error"); }

/*
 * Recursive implementation integer addition.
 *
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 *
 */

extern int __VERIFIER_nondet_int(void);

int addition(int m, int n) {
    if (n == 0) {
        return m;
    }
    if (n > 0) {
        return addition(m+1, n-1);
    }
    if (n < 0) {
        return addition(m-1, n+1);
    }
}


int main(int argc, char** argv) {
    int m =atoi(argv[1]);
//    klee_make_symbolic(&m, sizeof(int), "m");
    if (m < 0 || m > 1073) {
        // additional branch to avoid undefined behavior
        // (because of signed integer overflow)
        return 0;
    }
    int n =atoi(argv[2]);
//    klee_make_symbolic(&n, sizeof(int), "n");
    if (n < 0 || n > 1073) {
        // additional branch to avoid undefined behavior
        // (because of signed integer overflow)
        return 0;
    }
    int result = addition(m,n);
    if (__cpr_choice("L290", "bool", (int[]){m,n, result}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0) ) {
        return 0;
    } else {
        CPR_OUTPUT("obs", "i32", result - (m + n));
        ERROR: {reach_error();abort();}
    }
}