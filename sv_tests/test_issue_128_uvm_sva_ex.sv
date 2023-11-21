import uvm_pkg::*;  `include "uvm_macros.svh"
module uvm_sva_ex;   // File ch4/asn_testuvm_sva_ex.sv
    bit clk, a, b, c, req, ack; 
    parameter CLK_HPERIOD = 10;
    string tID="UART ";
    initial begin : clk_gen forever #CLK_HPERIOD clk <= !clk; end : clk_gen
    default clocking def_cb @ (posedge clk);  endclocking : def_cb
    ap_LOW: assert property(a) else
        `uvm_info(tID,$sformatf("%m : error in a %b", a), UVM_LOW); // Line 9
    ap_MEDIUM: assert property(a) else
        `uvm_info(tID,$sformatf("%m : error in a %b", a), UVM_MEDIUM); // Line 11
    ap_HIGH: assert property(a) else
        `uvm_info(tID,$sformatf("%m : error in a %b", a), UVM_HIGH);   // Line 13
    ap_FULL: assert property(a) else
        `uvm_info(tID,$sformatf("%m : error in a %b", a), UVM_FULL);   // Line 15
    ap_test2: assert property(a) else
        `uvm_error(tID,$sformatf("%m : error in a %b", a));       // Line 17
    ap_handshake0 : assert property ($rose(req) |=> ##[0:4] ack) else
        $error(tID, $sformatf("%m req = %0h, ack=%0h",                // Line 19
                       $sampled(req), $sampled (ack)));   
    ap_handshake : assert property ($rose(req) |=> ##[0:4] ack) else
        `uvm_error(tID, $sformatf("%m req = %0h, ack=%0h",            // // Line 22
              $sampled(req), $sampled (ack)));      


    initial begin
       
        req = 0; 
        ack = 1; 
        a = 1; 
       #10;req = 1; 
        ack = 1; 
        a = 1;
       
        #100; 
        $finish
    end                                                                               


endmodule : uvm_sva_ex