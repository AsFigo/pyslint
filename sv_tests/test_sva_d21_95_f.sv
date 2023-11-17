
module d21(); 
timeunit 1ns;
timeprecision 100ps;
reg read_xctn,frame,trdy;
bit clk;
`define false 1'b0

initial forever #10 clk=!clk; 
default clocking cb_clk @ (posedge clk);  endclocking 

property pReadTrdyFrame; 
	@ (posedge clk) not  ($rose(read_xctn) ##1 !frame[*0:10] ##1 frame ##1 trdy); 
endproperty : pReadTrdyFrame

property pReadTrdyFrame2; 
	@ (posedge clk) $rose(read_xctn) ##1 !frame[*0:10] ##1 frame ##1 trdy |-> `false; 
endproperty : pReadTrdyFrame2



property pReadTrdyFrame3; 
	@ (posedge clk) $rose(read_xctn) ##1 !frame[*0:10] ##1 frame |=> trdy ##0 `false; 
endproperty : pReadTrdyFrame3

d21ass1 : assert property(pReadTrdyFrame);
d21ass2 : assert property(pReadTrdyFrame2);
d21ass3 : assert property(pReadTrdyFrame3);

initial begin
	read_xctn = 0; 
	frame = 0; 
	trdy = 0;
	##1; read_xctn = 1; 
	frame = 1; 
	trdy = 1;

	##10; $finish;
end


endmodule : d21
