#include "svdpi.h"
void myFunction1(const svOpenArrayHandle v)
{
int l1 = svLow(v, 1);
int h1 = svHigh(v, 1);
for(int i = l1; i<= h1; i++) {
    printf("\t%d", *((char*)svGetArrElemPtr1(v, i)));
}
printf("\n");
               }
