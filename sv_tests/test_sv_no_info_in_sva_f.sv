//----------------------------------------------------
//----------------------------------------------------
// SPDX-FileCopyrightText: Mehul Arvind Prajapati, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

module test_sv_no_info_in_sva_f;
  timeunit 1ns;
  timeprecision 1ns;
    logic clk;  
  logic req;
  
  initial forever #5 clk = ~clk;

  always @(posedge clk) begin
    if (req) begin
      // ... do something
    end
  end

  a_ap_bad: assert property (@(posedge clk) req |=> !req) else $info("SVA failed");

  /*initial begin
    $dumpfile("dump.vcd");
    $dumpvars(1, test_sv_no_info_in_sva_f);
  end*/
endmodule: test_sv_no_info_in_sva_f