module m;
  bit clk, a, b;
  
  property p_ex;
    @(posedge clk) a |=> b
    ;
  endproperty : p_ex
  
  property p_no_semi_ex;
    @(posedge clk) a |=> b
  endproperty : p_no_semi_ex
  
endmodule : m
