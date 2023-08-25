 module unused_field_f;

  logic a;
  //unsed field
  logic unused_signal;

  initial
  begin
    a=0;
    $display("value of a:%0d",a);
    //unused_signal=1;
    //$display("value of unused_signal:%0d",unused_signal);
  end
 endmodul