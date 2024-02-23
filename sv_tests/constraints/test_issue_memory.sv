class packet;
 // Declare random variables 'addr' and 'cntr'
 rand bit [31:0] addr;
 rand bit [2:0] cntr;

 // Constraint 'c1': When 'cntr' is 0, constrain 'addr' to be within range
['h0:'h100]
 constraint c1 { cntr == 0 -> addr inside {['h0:'h100]}; }

 // Constraint 'c2': When 'cntr' is 0, ensure 'addr' is not within range
['h20:'hE0]
 constraint c2 { cntr == 0 -> !(addr inside {['h20:'hE0]}); }

 // Constraint 'c3': Constrain the lower 2 bits of 'addr' to be 0
 constraint c3 { addr[1:0] == 0; }

 // Constraint 'c4': When 'cntr' is not 0, 'addr' increments by 4
 constraint c4 { cntr != 0 -> addr == const'(addr + 4); }

 // Function to be executed after randomization
 function void post_randomize();
 // Reset 'cntr' to 0 if it was incremented to a non-zero value
 if (cntr++ == 0)
 cntr = 0;
 endfunction
endclass
// Define a module named 'test'
module test;
 // Declare an instance 'pkt' of class 'packet'
 packet pkt = new;

 // Initialize and randomize the object 'pkt' and display its 'addr' value
 initial begin
 // Repeat randomization process 10 times
 repeat (10) begin
 // Randomize the object 'pkt'
 pkt.randomize();

 // Display the value of 'addr' using '%0h' format specifier
 $display("addr = %0h", pkt.addr);
 end
 end
endmodule
