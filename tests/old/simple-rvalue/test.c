#ifndef CPR_OUTPUT
#define CPR_OUTPUT(id, typestr, value) value
#endif

int main() {
  int x = 1;
  int y = 10;
  x = __cpr_choice("L8", "i32", (int[]){x, y}, (char*[]){"x", "y"}, 2, (int*[]){&x, &y}, (char*[]){"x", "y"}, 2);
  return CPR_OUTPUT("exitcode", "i32", x);
}
