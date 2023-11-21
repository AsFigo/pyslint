
module unexpectedB_5_2; 
timeunit 1ns;
timeprecision 100ps;
parameter IDLE = 2'b00;
parameter STATE1 = 2'b01;
parameter STATE2 = 2'b10;
parameter STATE3 = 2'b11;

//typedef enum {IDLE, STATE1, STATE2, STATE3}  state_enum;

reg [1:0] s_bits;
reg start;
reg clk;
initial begin
	clk = 1'b1;
	start = 1'b0;
	s_bits=IDLE;
	forever #10 clk = ~clk;
end
   property UNEXPECTED_PROP;
	   @ (posedge clk) 
	   start |=> s_bits == STATE1 ##1 s_bits == STATE2;
   endproperty : UNEXPECTED_PROP

   UA1: assert property (UNEXPECTED_PROP);

   default clocking @ ( posedge clk ); endclocking

   initial begin

	   for (int i=1; i<=5; i=i+1) begin
		   ##1 
		   s_bits <= IDLE;
	   end

	   start <= 1'b1;
	   ##1    
	   s_bits <= STATE1;
	   ##1 	
	   s_bits <= STATE2;
	   ##1
	   repeat (1) @(posedge clk);
	   $finish;
   end
   endmodule : unexpectedB_5_2
