class packet;
 // Declare a random 32-bit wide logic vector 'a'
 rand logic [31:0] a;
 
 // Define a post_randomize function to be executed after randomization
 function void post_randomize();
 // Iterate through the first half of the vector
 for (int i = 0; i < 16; i++) begin
 // Assign each element of the first half to its corresponding element 
in the second half
 a[i] = a[31 - i]; // Palindrome logic: mirror the first half to the 
second half
 end
 endfunction
endclass
// Define a module named 'test'
module test;
 // Declare an instance 'pkt' of class 'packet'
 packet pkt;
 
 // Initialize and randomize the object 'pkt'
 initial begin
 pkt = new(); // Instantiate the 'pkt' object
 pkt.randomize(); // Randomize the 'pkt' object
 
 // Display the randomized value of vector 'a'
 $display("Value of a: %b", pkt.a);
 end
endmodule