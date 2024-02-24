class packet;
 // Declare a dynamic array 'a' of unsigned integers
 rand int unsigned a[];
 // Define a constraint 'c1' to restrict the size of array 'a' to be within 
the range [7:10]
 constraint c1 { a.size inside {[7:10]}; }
 // Define a post_randomize function to initialize the elements of array 'a' 
after randomization
 function void post_randomize();
 // Initialize the first two elements of array 'a' with 0 and 1
 a[0] = 0;
 a[1] = 1;
 // Use a loop to calculate the Fibonacci sequence and assign values to 
the remaining elements of 'a'
 for (int i = 2; i < a.size; i++)
 a[i] = a[i-1] + a[i-2];
 endfunction
endclass
// Define a module named 'test'
module test;
 // Declare an instance 'pkt' of class 'packet'
 packet pkt;
 // Instantiate the 'pkt' object
 initial begin
 pkt = new(); // Initialize the object 'pkt'
 
 // Randomize the object 'pkt'
 pkt.randomize();
 // Display the randomized values of array 'a' using %p format specifier
 $display("%p", pkt);
 end
endmodule