class packet;
 // Declare a 2D array 'a' with dimensions 6x6, each element being 4 bits 
wide
 rand bit[3:0] a[5:0][5:0];
 // Declare another randomizable 4-bit wide variable 'b'
 rand bit[3:0] b;
 // Define a constraint 'c1' to limit the values of 'b' to the range 0 to 9
 constraint c1 {b inside{[0:9]};}
 // Define a constraint 'c2' that applies to each element of the 2D array 
'a',
 // ensuring all values are within the range 0 to 9
 constraint c2{foreach (a[i,j]){
 a[i][j] inside {[0:9]};}}
 // Define a constraint 'c3' that applies a special condition to the array 
'a'
 // If an element is on the main diagonal (i==j) or the anti-diagonal (i+j 
== 5),
 // it must be equal to 'b'
 constraint c3{foreach (a[i,j]){
 if(i==j || (i+j == 5)){
 a[i][j]==b;}}}
endclass
// Define a module named 'test'
module test;
 // Instantiate an object 'pkt' of class 'packet'
 packet pkt = new();
 initial begin
 // Randomize the object 'pkt' and then print the values of array 'a' and 
variable 'b'
 pkt.randomize();
 // Iterate through the 2D array 'a' to display its elements
 foreach (pkt.a[i,j])
 begin
 $display("a[%0d][%0d] = %0d", i, j, pkt.a[i][j]);
 end
 // Display the entire array 'a' using the %p format specifier for 
debugging
 $display("%p", pkt.a);
 // Display the value of 'b'
 $display("%d", pkt.b);
 end
endmodule
