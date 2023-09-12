#include "svdpi.h"
DPI_DLLESPEC
int myFunction1(int j, int* o)
{
*o = j /2;
return 0;
}
DPI_DLLESPEC
void myFunction2(int i, int j, int* o)
{
*o = i+j;
return;
}
