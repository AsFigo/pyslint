module dff_latch_f (input d,
              input rstn,
              input clk,
              output reg q);

    always @ (posedge clk or negedge rstn)
       if (rstn)
          q <= d;
        //else part is missing latch get inferred
endmodule