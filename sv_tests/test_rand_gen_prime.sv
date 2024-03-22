class packet;
 
 rand bit[7:0] a[10];
 int b[10];
 
 // Define a function to calculate prime numbers and store them in array 'b'
 function void pre_randomize();
 int k = 0; // Initialize index for array 'b'
 
 // Loop to iterate through numbers from 7 to 200 with a step of 10
 for (int i = 7; i <= 200; i += 10) begin
 int c = 0; // Initialize a flag to check for prime
 
 // Loop to check if 'i' is a prime number
 for (int j = 2; j <= i/2 + 1; j++) begin
 // If 'i' is divisible by 'j', set the flag and break the loop
 if (i % j == 0) begin
 c = 1;
 break;
 end
 end
 
 // If 'c' is 0, 'i' is a prime number, so store it in array 'b'
 if (c == 0) begin
 b[k] = i;
 k++; // Increment the index for array 'b'
 end
 end
 endfunction
 
 // Define a constraint 'c1' to ensure that elements of 'a' match with prime 
numbers from 'b'
 constraint c1 {
 foreach (a[i]) // Iterate over each element 'a[i]' in array 'a'
 a[i] == b[i]; // Constrain 'a[i]' to be equal to the corresponding 
element in array 'b'
 }
endclass
// Define a module named 'test'
module test;
 // Declare an instance 'pkt' of class 'packet'
 packet pkt = new;
 
 // Initialize and randomize the object 'pkt'
 initial begin
 void'(pkt.randomize());
 
 // Display the randomized values of array 'a' using '%0p' format 
specifier
 $display("%0p", pkt.a);
 end
endmodule