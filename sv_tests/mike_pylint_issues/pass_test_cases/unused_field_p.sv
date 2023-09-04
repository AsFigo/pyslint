 module unused_field_p;

  logic a;
  //unused field now used
  logic unused_signal;

  initial
  begin
    a=0;
    $display("value of a:%0d",a);
    unused_signal=1;
    $display("value of unused_signal:%0d",unused_signal);
  end
 endmodule
                  