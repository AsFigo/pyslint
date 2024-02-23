class packet;
 // Declare a 2D array 'a' of random bits with dimensions 4x4, each element 
being 3 bits wide
 rand bit [2:0] a[4][4];
 // Define a constraint 'c1' on the elements of the 2D array 'a'
 constraint c1 {
 // Iterate over each element in the array using two nested foreach loops
 foreach (a[i,j])
 foreach (a[k,l])
 {
 // If the row indices i and k are different, ensure the elements in 
the same column j are different
 i != k -> a[i][j] != a[k][j];
 
 // If the column indices j and l are different, ensure the elements 
in the same row i are different
 j != l -> a[i][j] != a[i][l];
 }
 };
endclass
// Define a module named 'test'
module test;
 // Instantiate an object 'pkt' of class 'packet'
 packet pkt = new();
 initial begin
 // Randomize the object 'pkt' and display its contents
 pkt.randomize();
 $display("%p", pkt); // %p prints the variable in a format that shows 
both the structure and the value
 end
 
endmodule