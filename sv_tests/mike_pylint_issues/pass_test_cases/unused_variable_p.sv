module unused_variable_p;

  int a;
  int b;

  initial
  begin
  //all variables are used
    a=0;
    $display("value of a:%0d",a);
    b=1;
    $display("value of b:%0d",b);
  end
 endmodule