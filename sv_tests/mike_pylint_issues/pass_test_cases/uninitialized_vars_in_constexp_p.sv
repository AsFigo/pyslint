module uninitialized_vars_in_constexp_p;
int data;
const int unsigned my_const = 10; // This is a valid constant

initial begin
        data = my_const;
        $display("data:%0d",data);
end

endmodule