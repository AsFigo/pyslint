class diagonal;
 // Declare a 3x3 array 'array' of 4-bit width elements
 rand reg [3:0] array[2:0][2:0];
 
 // Constraint 'c': Set diagonal elements to zero, and non-diagonal elements 
to non-zero values
 constraint c {
 foreach (array[i,j]) {
 if (i == j) // Check if 'i' is equal to 'j' (diagonal element)
 array[i][j] == 0; // Set diagonal elements to zero
 else
 array[i][j] != 0; // Set non-diagonal elements to non-zero values
 }
 }
endclass
// Define a module named 'top'
module top;
 // Declare an instance 'd' of class 'diagonal'
 diagonal d;
 
 // Initialize and randomize the object 'd' and display its 'array' values
 initial begin
 // Create an instance of class 'diagonal'
 d = new();
 
 // Randomize the object 'd'
 d.randomize();
 
 // Display the randomized values of array 'array' using '%p' format 
specifier
 $display("array = %p", d.array);
 end
endmodule