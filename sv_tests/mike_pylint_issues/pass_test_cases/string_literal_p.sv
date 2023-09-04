module string_literal_p;

  initial begin
    string strValue = "Hello, World!";
    integer intValue;

    // Try to assign the string value to an integer
    intValue = int'(strValue);//type casting from string to integer
    $display("String Value: %s", strValue);
    $display("Integer Value: %d", intValue);
  end

endmodule