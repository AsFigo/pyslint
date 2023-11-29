
module m10_7;
    bit clk, req, ack, busy;
    bit[2:1] id=3'b000; 
    initial forever #10 clk=!clk; 
    default clocking cb_clk @ (posedge clk);  endclocking 
  
    initial begin
      ##10;
      req = 1;
      ##2;
      ack = 1;
      ##10;
      $finish (2);
    end
    ap_ReqAckBusy: assert property($rose(req) |=>  busy s_until_with ack ); // ch9/ m9_6
    /*
Error-[SVA-SONS] Strong operator not supported
../m10_7.sv, 7
m10_7, "(busy s_until_with ack)"
  Strong operator used in assertion 'ap_ReqAckBusy' is not supported in this 
  context.

  */    
endmodule
