class packet;
 // Declare a randomizable array 'a' with 10 elements
 rand int a[10];
 // Declare another randomizable array 'b' with 9 elements
 rand int b[9];
 
 // Define a constraint 'c1' on arrays 'a' and 'b'
 constraint c1 {
 // Iterate over each element in array 'a'
 foreach (a[i]) {
 // Assign values to 'a' based on index parity
 if (i % 2 == 0)
 a[i] == i * -5; // If the index is even, assign the value as the 
negative multiple of the index
 else
 a[i] == i * 5; // If the index is odd, assign the value as the 
positive multiple of the index
 
 // Ensure that each element in 'b' is equal to the next element in 'a'
 b[i] == a[i + 1];
 }
 }
endclass
// Define a module named 'test'
module test;
 // Instantiate an object 'pkt' of class 'packet'
 packet pkt = new();
 
 initial begin
 // Randomize the object 'pkt'
 pkt.randomize();
 // Display the values of array 'b' after randomization
 $display("%p", pkt.b);
 end
endmodule