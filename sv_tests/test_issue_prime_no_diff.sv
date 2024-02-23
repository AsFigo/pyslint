class packet;
 // Declare a dynamic array 'a' of 8-bit width
 rand bit [7:0] a[];
 // Declare an integer variable 'i' for loop iteration
 int i;
 // Define a constraint 'prime_numbers' to generate prime numbers and store 
them in array 'a'
 constraint prime_numbers {
 // Constrain the size of array 'a' to be exactly 20 elements
 a.size == 20;
 
 // Iterate over each element 'a[i]' in the array using 'foreach' loop
 foreach (a[i])
 // Check if 'i' is a prime number
 if (!((i % 2 == 0 && i == 2) || (i % 3 == 0 && i != 3) || (i % 4 == 0
&& i != 4) || (i % 5 == 0 && i != 5) || (i % 6 == 0 && i != 6) || (i % 7 == 0
&& i != 7) || (i % 8 == 0 && i != 8) || (i % 9 == 0 && i != 9)))
 // If 'i' is a prime number, assign it to 'a[i]'
 a[i] == i;
 else
 // If 'i' is not a prime number, assign 1 to 'a[i]'
 a[i] == 1;
 }
endclass
// Define a module named 'test'
module test;
 // Declare an instance 'pkt' of class 'packet'
 packet pkt;
 // Instantiate the 'pkt' object
 initial begin
 // Initialize the 'pkt' object
 pkt = new();
 
 // Randomize the 'pkt' object, applying constraints defined in the 
'packet' class
 pkt.randomize();
 
 // Display the randomized values of array 'a' using '%p' format specifier
 $display("pkt = %p", pkt.a);
 end
endmodule