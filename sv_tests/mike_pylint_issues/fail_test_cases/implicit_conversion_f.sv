module implicit_conversion_f();
    reg [3:0] a = 4'd7;//a 4bit variable
    reg [2:0] b = 3'd5;//3 bit variable
    reg [4:0] result;

    always_comb begin
        result = a + b;//width mismatch while adding a and b
    end

    initial begin
        $display("Result: %d", result);
    end
endmodule