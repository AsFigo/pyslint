
module m;
  
  bit clk,a,b;

  property p_empty_sequence_2;
    @(negedge clk)
    (a |-> a[*0:3]);
  endproperty : p_empty_sequence_2

  a_p_empty_sequence_2 : assert property (empty_sequence_2);
endmodule
