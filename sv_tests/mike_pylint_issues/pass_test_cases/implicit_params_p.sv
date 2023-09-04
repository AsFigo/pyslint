module implicit_params_p();

parameter m1 = 2;

initial
begin
        $display("value of m1:%0d",m1);
end
endmodule

module tb;

  implicit_params_p t1();
  defparam t1.m1 = 10;//explicit parameter redefine
endmodule