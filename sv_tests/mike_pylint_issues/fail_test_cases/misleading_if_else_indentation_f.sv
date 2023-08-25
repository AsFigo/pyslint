module misleading_if_else_indentation_f;
    reg a, b;
    reg result;

    initial begin
        a = 1;
        b = 0;

        if (a)
            if (b)
            result = 0;
        else
            result = 1;//else belongs to the inner if not the outer if

        $display("Result: %b", result);
    end
endmodule