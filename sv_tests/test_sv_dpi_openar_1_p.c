
#include <svdpi.h>

// DPI function to calculate the sum of elements in an array
int c_sum(const svOpenArrayHandle *input_array) {
    int sum = 0;
    int len = svSize(input_array, 1);
     int i = 0;
  
    for ( i = 0; i < len; i++) {
        int value;
        value = &input_array[i] + 1;
      printf ("i: %d inp: %d &inp: %d\n", i, input_array[i], &input_array[i]);
       printf("DPI: %d \n", *((char*)svGetArrElemPtr1(input_array, i)));
        sum += value;
    }

    return sum;
}
