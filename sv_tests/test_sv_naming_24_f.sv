class randvar;
rand bit [7:0] var1, var2, var3, var4;
endclass

// Define a module called rand_methods
module rand_methods;
initial begin
// Create an object of the randvar class called pkt
randvar pkt;

// Allocate memory for the pkt object
// pkt = new();
//Lint must catch this violation as the pkt object is not allocated with any memory

// Call the randomize method to assign random values to the variables in pkt
pkt.randomize();
// Display the randomly generated values of the variables in pkt using the $display function
$display("\t VAR1 = %0d \t VAR2 = %0d \t VAR3 = %0d \t VAR4 = %0d ",pkt.var1, pkt.var2, pkt.var3, pkt.var4);
end
endmodule
