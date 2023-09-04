module empty_if_new_p;
  reg a;

  initial begin
    a = 1'b1;
    if (a) begin
      $display("Not an empty if");//if is not empty
    end
  end

endmodule