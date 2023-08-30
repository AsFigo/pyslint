module misleading_if_else_indentation_p;
    reg a, b;
    reg result;

    initial begin
        a = 1;
        b = 0;

        if (a) begin
            if (b)
            result = 0;
           else
            result = 1;//else belongs to the inner if not the outer if properly indented
        end
        $display("Result: %b", result);
    end
endmodule
