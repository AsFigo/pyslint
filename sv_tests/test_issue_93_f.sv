module d17(); 
       timeunit 1ns;
       timeprecision 100ps;
       reg read,write,rd_served,interrupt,wr_served;
       bit clk;
       initial forever #10 clk=!clk; 
       default clocking cb_clk @ (posedge clk);  endclocking  
       property pNeverReadWrite;  
	   @ (posedge clk) not (read && write); 
       endproperty : pNeverReadWrite
       d17assert : assert property (pNeverReadWrite);
       property pReadSchedule;
	   @ (posedge clk)  $rose(read) |-> (##[1:5]rd_served) or (##[1:5] interrupt);
       endproperty : pReadSchedule
       d17assert1 : assert property (pReadSchedule);
       property pWriteSchedule;
	   @ (posedge clk)  $rose(write) |-> (##[1:5]wr_served) or (##[1:5] interrupt);
       endproperty : pWriteSchedule
       d17assert2 : assert property (pWriteSchedule);
       sequence  qNewInterrupt; 
	   @ (posedge clk) ##[0:$] $rose(interrupt);
       endsequence : qNewInterrupt
       d17assert3 : assert property (qNewInterrupt);

       initial begin
         #10 read = 1;
         write = 1;
         #10 read = 1;
         rd_served = 1;
         #10 read = 0;
         #10 write = 1;
         wr_served = 1;
         #10 write = 0;
         interrupt = 1;
         interrupt = 0;
         ##10;$finish;
       end
   endmodule :d17