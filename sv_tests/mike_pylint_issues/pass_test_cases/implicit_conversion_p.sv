module implicit_conversion_p();
    reg [3:0] a = 4'd7;
    reg [3:0] b = 4'd3;//explicit conversion of b from 3 bit to 4 bit
    reg [4:0] result;

    always_comb begin
        result = a + b;

end

    initial begin
        $display("Result: %d", result);
    end
endmodule