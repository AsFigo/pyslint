module self_assign_p;
  logic a = 0;

  initial begin
    a = 1; // recommended to avoid self-assignments and always use valid assignment statements with appropriate values else if we give a = a; then proper comments needed for self assignment
    $display("a = %0d", a);
  end
endmodule