module self_assign_f;
  logic a = 0;

  initial begin
    a = a; // Self-assignment
    $display("a = %0d", a);
  end
endmodule