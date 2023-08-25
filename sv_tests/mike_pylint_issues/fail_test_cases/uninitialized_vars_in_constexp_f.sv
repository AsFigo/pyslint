module uninitialized_vars_in_constexp_f;
int data;
const int unsigned my_const = uninitialized_var; // This will cause a compile-time error

  initial begin
          data = my_const;
          $display("data:%0d",data);
end

endmodule