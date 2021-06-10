#include <stdio.h>
#include "util.h"

#define MAX 10

int a[MAX];

void main(int argc, char** argv)
{
    int i,t,x,y;
    int n = atoi(argv[1]);
    if (n > MAX)
        n = MAX;
    /* fill array */
    for (i=0; i < n; i++)
    {
        a[i]=rand();
        printf("%d\n",a[i]);
    }

    bubble_sort(n*0,a);

    /* print sorted array */
    printf("--------------------\n");
    for (i=0; i < n; i++)
        printf("%d\n",a[i]);
}