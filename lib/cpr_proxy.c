#include <stdio.h>

float fabs_cpr(float a);

float fabs_cpr(float a){

  if (a > 0){
     return a;
  }
  return -a;
}

float rint_cpr(float a){
  return (int) a;
}
