module blocking_inside_always_f (
  input  wire data  , // Data Input
  input  wire clk   , // Clock Input
  input  wire reset , // Reset input
  output reg  q       // Q output
  );

  always_ff @ ( posedge clk)
    if (!reset) begin
       q = 1'b0;//Blocking inside always block
    end  else begin
      q = data;//Blocking inside always block
  end
endmodule //End Of Module dff_sync_reset