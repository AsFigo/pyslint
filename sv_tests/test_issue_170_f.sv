module test;
 
  function int divide(int dividend, int divisor);
    int i = dividend / divisor;
    automatic int a_i = dividend / divisor;
    static int s_i = dividend / divisor;
    int no_init;
    return i;
  endfunction
 
  function automatic int auto_f(int dividend, int divisor);
    int i = dividend / divisor;
    automatic int a_i = dividend / divisor;
    static int s_i = dividend / divisor;
    int no_init;
    return i;
  endfunction
 
  initial begin
    int j;
    j =divide(200,  64);
    $display("j=%0d", j);
  end
endmodule
