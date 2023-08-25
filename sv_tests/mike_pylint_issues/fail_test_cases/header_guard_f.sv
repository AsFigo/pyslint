//without header guard definition
module header_guard_f(
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