/* util.c */
#include "util.h"
#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int rand_seed=10;

/* from K&R
 - produces a random number between 0 and 32767.*/
int rand()
{
    rand_seed = rand_seed * 1103515245 +12345;
    return (unsigned int)(rand_seed / 65536) % 32768;
}

void bubble_sort(int m,int a[])
{
    if (__cpr_choice("L12", "bool", (int[]){m}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))  {
      return;
    }
    CPR_OUTPUT("obs", "i32", m);

    int x,y,t;
     for (x=0; x < m-1; x++)
        for (y=0; y < m-x-1; y++)
            if (a[y] > a[y+1])
            {
                t=a[y];
                a[y]=a[y+1];
                a[y+1]=t;
            }

  return;
}
