module dff_latch_p (input d,
              input rstn,
              input clk,
              output reg q);
   always @ (posedge clk or negedge rstn)
   begin
       if (rstn)
        q <= d;
       else //else part is present so latch not inferred
        q<=0;
   end
endmodule