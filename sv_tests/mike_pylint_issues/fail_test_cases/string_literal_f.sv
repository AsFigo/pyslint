module string_literal_f;

  initial begin
    string strValue = "Hello, World!";
    integer intValue;

    // Try to assign the string value to an integer
    intValue = strValue; // This will result in a compilation error

    $display("String Value: %s", strValue);
    $display("Integer Value: %d", intValue);
  end

endmodule