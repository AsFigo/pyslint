class packet; 
 rand int unsigned a;
 int q[$] = {0};
 
 // Declare integer variables 'var1' and 'var2'
 int var1;
 int var2;
 
 // Define a post_randomize function to be called after randomization
 // This function manipulates the variables and displays a postrandomization value
 function void post_randomize();
 // Declare and initialize a local integer variable 'b'
 int b = 9;
 
 // Remove the last element from array 'q' and assign it to 'var1'
 var1 = q.pop_back();
 
 // Calculate 'var2' based on 'var1' and 'b'
 var2 = (var1 * 10) + b;
 
 // Insert 'var2' at the front of array 'q'
 q.push_front(var2);
 
 // Display the post-randomization value of 'var2'
 $display("POST_RANDOMIZATION::value=%d", var2);
 endfunction
 // Define a constraint 'c1' to ensure that 'a' is equal to the postrandomization value 'var2'
 constraint c1 { a == var2; }
 
 // Define a display function to display the value of 'a'
 function void display();
 $display("Display value::a=%d", a);
 endfunction
endclass
// Define a module named 'test'
module test;
 initial begin
 // Create an instance 'pkt' of class 'packet'
 packet pkt = new();
 
 // Repeat the randomization process 9 times
 repeat(9) begin
 // Randomize the object 'pkt'
 pkt.randomize();
 
 // Call the display function to display the randomized value of 'a'
 pkt.display();
 end
 end
endmodule