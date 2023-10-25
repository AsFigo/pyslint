
module m;
  
  bit clk,a,b;
  
property ab;
  @(posedge clk) a |=> b[=0];
 endproperty

  a_p_ab : assert property (ab);
    
endmodule
