
module test2_5_4;
    timeunit 1ns;
    timeprecision 1ns;

    logic clk=1, req=0, ack=0, xfr=0;
    int max=4; 

    property pReqAck(req, ack, upper); 
        int v_ack_count;  //  local variable for the ack count 
        ($rose(req), v_ack_count = 1)  |=>  // If request, initialize  counter  
          (v_ack_count < upper && !ack, v_ack_count += 1)[*0:$]  ##1 ack;                     
    endproperty : pReqAck
    apReqAck : assert property(@ (posedge clk) pReqAck($rose(req), ack, max));


    property pAckDone(ack, xfr, rep); 
        int v_xfr_count;  //  local variable for the xfr count 
        (ack, v_xfr_count = 1) |=> // Reset v_xfr_count to count number of data transfers 
        sync_reject_on(!xfr)  // If no transfer, then it's an error 
        //(xfr && (v_xfr_count < rep), v_xfr_count += 1)[*0:$] // Illegal 
        // ##1 v_xfr_count==rep; // ends the repeat
        v_xfr_count==rep or 
        ((xfr && (v_xfr_count < rep), v_xfr_count += 1)[*1:$] ##1 v_xfr_count== 
        rep); 
    endproperty : pAckDone
    apAckDone : assert property(@ (posedge clk) pAckDone($rose(ack), xfr, 2));  

    default clocking @(negedge clk); 
    endclocking
    always @ (posedge clk) begin
        assert( std :: randomize(req, ack, xfr));
    end
    initial forever #5clk=!clk;
initial begin
   ##1  req=1; ack=1; xfr=0;
   ##1   req=1; ack=1; xfr=1;
   ##1 req=0; ack=0; xfr=1;
   ##1  req=0; ack=0; xfr=1;
   ##1  req=0; ack=0; xfr=0;
   ##1  req=0; ack=0; xfr=0;
 
  repeat(10);##1
  $finish; 
  
end

endmodule : test2_5_4  

