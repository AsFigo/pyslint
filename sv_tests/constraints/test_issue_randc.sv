class packet;
 // Declare a dynamic array 'a' of 11-bit width elements
 bit [10:0] a [$];

 // Declare a random 11-bit width variable 'b'
 rand bit [10:0] b;
 // Constraint 'c' ensures that 'b' is not inside 'a'
 constraint c { !(b inside {a}); }
 // Constraint 'c2' constrains the range of 'b' to be between 2 and 20
 constraint c2 { b inside {[2:20]}; }
 // Function to be executed after randomization
 function void post_randomize();
 // Add 'b' to the front of array 'a'
 a.push_front(b);

 // If the size of 'a' exceeds 10, remove the last element
 if (a.size() == 10)
 a.delete();
 endfunction
endclass
// Define a module named 'test'
module test;
 // Initialize and randomize the object 'pkt' and display its values
 initial begin
 // Create an instance 'pkt' of class 'packet'
 packet pkt = new;
 // Repeat the randomization process 10 times
 repeat (10) begin
 // Randomize the object 'pkt'
 void'(pkt.randomize());

 // Display the value of 'b' and the elements of 'a' for each iteration
 $display("b is %d %b ", pkt.b, pkt.b);

 // Iterate over each element of 'a' and display its value along with
its index
 foreach (pkt.a[i])
 $display("a[%0d] value is %d", i, pkt.a[i]);
 end
 end
endmodule
