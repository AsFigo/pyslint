module counter; 
timeunit 1ns; 
timeprecision 100ps;

logic clk=0, reset_n=0, go = 0;
int cntr =0;

property pCounterMaxed;
	@ (posedge clk) disable iff (!reset_n)
	go |=> (cntr <= 3);
endproperty : pCounterMaxed

apCounterMaxed : assert property (pCounterMaxed) else 
	$display("%0t SVA_ERR: Counter exceeded 3, cntr %0d; sampled(cntr) %0d ",$time, cntr, $sampled(cntr));

  initial  
  begin : clk_gen
	  clk <= 0;  forever #10 clk <= ~clk;
  end

  default clocking @ ( negedge clk ); endclocking 

  initial
  begin : stim
	  ##5;
	  ##1; // sync to neg edge to avoid data change in active clk edge
	  reset_n = 1;
	  go = 1;
	  repeat (3) ##1;
	  $finish;
  end : stim

  always @ (posedge clk)
	  if (!reset_n)  cntr <=1'b0;
	  else  cntr <= cntr + 1'b1;
endmodule : counter 