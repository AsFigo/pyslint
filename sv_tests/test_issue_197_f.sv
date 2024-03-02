module test_issue_197_f

// Three-dimensional array
logic [7:0] dim4_array[4][4]
[4];
logic [7:0] multi_dim_array[4][4];
logic [7:0] dim2_array[4];
logic [7:0] dim1_array;

initial begin
    // Attempt to write the three-dimensional array to a file (not supported)
    $writememb("multi_dim_array_dump.bin", multi_dim_array);
end

endmodule // logic
