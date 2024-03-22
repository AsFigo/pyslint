class packet;
 // Define an enumeration type 'port_num' with three values: port_0, port_1, 
port_2
 typedef enum {port_0, port_1, port_2} port_num;
 // Declare a randomizable variable 'port' of type 'port_num'
 rand port_num port;
 
 // Declare a randomizable 8-bit wide variable 'addr'
 rand bit [7:0] addr;
 
 // Define a constraint 'c1' on 'port' and 'addr'
 constraint c1 {
 // Constraints on 'addr' based on the value of 'port'
 port == port_0 -> addr inside {[0:10]}; // If 'port' is port_0, 'addr' 
should be in the range [0:10]
 port == port_1 -> addr inside {[11:20]}; // If 'port' is port_1, 'addr' 
should be in the range [11:20]
 port == port_2 -> addr inside {[21:30]}; // If 'port' is port_2, 'addr' 
should be in the range [21:30]
 }
endclass
// Define a module named 'test'
module test;
 // Instantiate an object 'pkt' of class 'packet'
 packet pkt = new();
 
 initial begin
 // Repeat the randomization process 10 times
 repeat(10) begin
 // Randomize the object 'pkt'
 pkt.randomize();
 // Display the randomized values of 'port' and 'addr'
 $display("%p", pkt);
 end
 end
endmodule