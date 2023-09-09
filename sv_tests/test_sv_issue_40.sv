//Constraint to generate a clock
class clk;
  rand bit a;
  constraint c1 {
    if(const'(a)) 
      a==0;
    else
      a==1;
  }
endclass
//const casting will add an implicit order on variable and it will retain it's value from last randomization

module top;
  clk h = new;
  initial begin
    repeat(20) begin
      h.randomize();
      $write("%0d", h.a); end
  end
endmodule
