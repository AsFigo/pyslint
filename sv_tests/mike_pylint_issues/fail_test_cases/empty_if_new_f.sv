module empty_if_new_f;
  reg a;

  initial begin
    a = 1'b1;
    if (a) begin
      // Empty if body
    end
  end

endmodule