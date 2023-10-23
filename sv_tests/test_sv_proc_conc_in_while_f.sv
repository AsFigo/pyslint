
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
  property a_imp_b;
    a |-> b;
  endproperty

  //----------------------//
  always @(posedge clk) begin
    always_asrt: assert property(always_pp);
  end

  //----------------------//
  initial begin
    begin : bef
      ib_asrt: assert property(a_imp_b);
    end : bef
    while (int i=0; i < 10; i++) begin
      wh_asrt: assert property(a_imp_b);
    end
    ia_asrt: assert property(a_imp_b);
  end

  //----------------------//     
  initial begin
    #2 a=1; b=0;
    #20 $finish;
  end

endmodule
