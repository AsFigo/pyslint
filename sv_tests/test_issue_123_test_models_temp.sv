module temp;
    timeunit 1ns;
    timeprecision 100ps;
    logic clk=0,clk0,clk2,req=0,ack=0,done=0,status_reg=0;
    default clocking cb_clk @ (posedge clk);  endclocking 
    apReqAckDoneSuccess: assert property(
      first_match($rose(req) ##[1:5] ack ##[1:100] done)
            |-> (status_reg == 1'b0) );
    apReqAckDoneFail: assert property(
        $rose(req) |=> !done[*105] |-> (status_reg == 1'b1) );
      
    logic a = 1, b = 1;
    logic [3:0] i = 1, j = 1;
    initial begin
        $display("a=%b, b=%b, i=%b, j=%b", a, b, i, j);
        $display("!a=%b, ~b=%b, ~i=%b, j=%b", !a, ~b, ~i, j);
        $display("a&b=%b, a&&b=%b, i&j=%b, j=%b", a & b, a && b, i & j, j);
        ap_a_is1: assert (!a)  $info ("PASS !a -- a=%b, b=%b, i=%b, j=%b", a, b, i, j);
        else $info("FAIL !a -- a=%b, b=%b, i=%b, j=%b", a, b, i, j);
        ap_j_is1: assert (~j) $info("PASS ~j -- a=%b, b=%b, i=%b, ~j=%b", a, b, i, ~j);
        else $info("FAIL ~j -- a=%b, b=%b, i=%b, ~j=%b", a, b, i, ~j);
        ap_j_is1_logical: assert (!j) $info("PASS !j -- a=%b, b=%b, i=%b, !j=%b", a, b, i, !j
                );
        else $info("FAIL !j -- a=%b, b=%b, i=%b, j=%b", a, b, i, !j);
    end
    initial forever #5 clk=!clk;
    
      initial
        begin
        
           #5; req=1;
           #5;ack=1;req=0;
           #50;done=1;status_reg =1'b0;req=1;
           #10;done=0;
           #105;done=0;status_reg =1'b1;
          #5;done=1;
        
          #500;$finish;
       end
        
endmodule