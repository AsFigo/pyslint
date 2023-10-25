
module m;

  bit clk,a,b;

  property p_empty_sequence_1;
    @(negedge clk)
    (a[*0]);
  endproperty : p_empty_sequence_1

  a_p_empty_sequence_1 : assert property (p_empty_sequence_1);
endmodule
