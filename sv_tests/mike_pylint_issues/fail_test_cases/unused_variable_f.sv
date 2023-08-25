 module unused_variable_f;

  int a;
  int b;//unused variable b

  initial
  begin
    a=0;
    $display("value of a:%0d",a);
  end
 endmodule