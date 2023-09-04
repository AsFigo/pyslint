module test_new_m;
   bit req,grnt;
   bit clk;

   property p_req_cycle;
           @(posedgeclk) $rose (req) |-> ##[1:3] grnt;
   endproperty : p_req_cycle

   a_new : assert property ((@posedge clk) p_req_cycle);
       else $error ("Fail");


endmodule : test_new_m
