module mymodule();
import "DPI-C" function void myFunction1(input int v[]);
int arr[4];
int dynArr[];
initial begin
arr = '{4, 5, 6, 7};
myFunction1(arr);
dynArr = new[6];
dynArr = '{8, 9, 10, 11, 12, 13};
myFunction1(dynArr);
end
endmodule
