module shadowing_names_f;
  int data = 5;

  initial begin
    int data = 10; // This shadows the outer 'data' variable
    $display("Inner data: %0d", data); // This will print the inner 'data'
  end

  initial begin
    $display("Outer data: %0d", data); // This will print the outer 'data'
  end
endmodule