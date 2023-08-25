module dangling_else_new_p;

  // Declare the signals
  reg a, b, c, d;

  initial begin
    a = 1; // Change these values to test different scenarios
    b = 1;

    // Execute the nested if-else code with an error
    if (a) begin
      if (b) begin
             c = 1;
             end
    else
      d = 1;
         end

    // Display results
    $display("a = %b, b = %b, c = %b, d = %b", a, b, c, d);

  end

endmodule