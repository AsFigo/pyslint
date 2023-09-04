`ifndef MY_HEADER_GUARD
`define MY_HEADER_GUARD

module header_guard_p (


  input clk,
  input rst,
  output reg [7:0] data
);

  always @(posedge clk) begin
    if (rst) begin
      data <= 0;
    end else begin
      data <= data + 1;
    end
  end

endmodule

`endif