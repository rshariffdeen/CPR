#include <stdio.h>

#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main(int argc, char *argv[]) {
  char buffer[10];
  char *filepath = argv[1];
  char *option = argv[2];
  FILE *fp = fopen(filepath, "r");
  fread(buffer,sizeof(int),1,fp);
  fclose(fp);
  int y = buffer[0] - 48;
  printf("Option: %s, Number: %d\n", option,y);
  if (__cpr_choice("L9", "bool", (int[]){y}, (char*[]){"x"}, 1, (int*[]){}, (char*[]){}, 0))
    return -1;
  CPR_OUTPUT("obs", "i32", y);
  int res = 100 /y;
  return 0;
}