module top (
  input clk,
  input rst,
  output reg [15:0] apb_wdata,
  output reg int apb_addr
);

  import "DPI-C" context task gen_val_in_c (
          output int addr,
		  output data);

  always @(posedge clk) begin
    if (rst) begin
      apb_wdata <= 0;
      apb_addr <= 0;
    end else begin
      gen_val_in_c(apb_addr, apb_wdata);
    end
  end

endmodule
