#include <stdio.h>

int main(int argc, char** argv){
    int i = atoi(argv[1]);
    int j = atoi(argv[2]);
    int k;
    klee_make_symbolic(&k, sizeof(k), "k");
    if (i > 5)
        printf("Statement One\n");
    else
        printf("Statement Two\n");

    if (j > 10)
        printf("Statement Three\n");
    else
        printf("Statement Four\n");

    if (k > 20)
        printf("Statement Five\n");
    else
        printf("Statement Six\n");

    printf("\nValues: i=%d, j=%d, k=%d\n\n", i, j, k);
    return 0;

}