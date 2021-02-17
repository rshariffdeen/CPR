#include <stdio.h>

#ifndef TRIDENT_OUTPUT
#define TRIDENT_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  int x;
  char *filepath = argv[1];
  FILE *fp = fopen(filepath, "r");
  fread(&x,sizeof(int),1,fp);
  fclose(fp);
  int y = __trident_choice("L9", "i32", (int[]){x}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0);
  TRIDENT_OUTPUT("obs", "i32", y - (x*x));
  return 0;
}