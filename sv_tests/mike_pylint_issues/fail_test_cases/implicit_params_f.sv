module implicit_params_f();

parameter m1 = 2;

initial
begin
        $display("value of m1:%0d",m1);
end
endmodule

module tb;

implicit_params_f #(5) t1();//implicit parameter redefine

endmodule