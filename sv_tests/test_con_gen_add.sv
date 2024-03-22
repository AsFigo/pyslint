class packet;
 
 // Declare a 16-bit randomizable variable 'a'
 rand bit[15:0] a;
 
 // Define a constraint 'c1' on 'a'
 constraint c1 {
 // Ensure that the total number of 1's in 'a' equals 9
 $countones(a) == 9;
 
 // Further constraints applied to every triplet in 'a' to ensure
 // specific patterns are not formed
 foreach (a[i]) {
 // Check only up to the 14th bit to avoid out-of-bounds access
 if (i < 14) {
 // Ensure that no three consecutive bits form the pattern 000
 { a[i], a[i+1], a[i+2] } != 3'b000;
 // Ensure that no three consecutive bits form the pattern 111
 { a[i], a[i+1], a[i+2] } != 3'b111; 
 }
 }
 }
endclass
// Define a module named 'test'
module test;
 
 // Instantiate an object 'pkt' of class 'packet'
 packet pkt = new();
 
 initial begin
 // Repeat the randomization and display process 10 times
 repeat(10) begin
 // Randomize 'pkt' according to its constraints
 pkt.randomize();
 // Display the 16-bit variable 'a' in binary format
 $display("%0b", pkt.a);
 end
 end
endmodule