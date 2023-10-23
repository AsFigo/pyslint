
module test;

bit clk;
bit a,b;

default clocking @(posedge clk); endclocking

always #1 clk = ~clk;

//----------------------//
  property always_pp;
    a |-> b;
  endproperty

  //----------------------//
  property forever_pp;
    a |-> b;
  endproperty

  //----------------------//
  always @(posedge clk) begin
    always_asrt: assert property(always_pp);
  end

  //----------------------//
  initial begin
    forever @(posedge clk)begin
      forever_asrt: assert property(forever_pp);
    end
  end

  //----------------------//     
  initial begin
    #2 a=1; b=0;
    #20 $finish;
  end

endmodule
