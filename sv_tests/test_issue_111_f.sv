
   module mq;
	bit clk, rd_25;
        int dataQ [$];
        int dataQsize; 
        property p_never_read_on_empty;
        not (dataQsize == 0 && rd_25);  
	// Legal in 1800-2012, may not yet be supported by all vendors (NYS)
       endproperty : p_never_read_on_empty
       assert property(@(posedge clk)  p_never_read_on_empty); 
     
       initial forever #5 clk = ~clk; 
       initial begin
          clk=0;dataQsize=0;rd_25=1;
          #5;dataQsize=10;rd_25=0;
          #10;$finish;
       end
   endmodule
