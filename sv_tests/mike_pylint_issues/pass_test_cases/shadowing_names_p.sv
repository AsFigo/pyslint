module shadowing_names_p;
  int data = 5;

  initial begin
           int local_data = 10; // Avoid naming conflict
           $display("Inner data: %0d", local_data); // This will print the inner 'local_data'
  end

  initial begin
    $display("Outer data: %0d", data); // This will print the outer 'data'
  end
endmodule