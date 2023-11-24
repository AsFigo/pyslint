module m; 
	bit a=0, b=0, go=0, clk=0; 
	initial begin 
		#100;
	    forever #5 clk=!clk; 
	end 
	ap_ab: assert property (@ (posedge clk)
       disable iff (!go) // if go==0, cancel checking asynchronously
              a |=> b);
	initial begin
         #5; go =1; a=1;
         #10;b=1;
	 #200;
            $finish;
         end
endmodule 