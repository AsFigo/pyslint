//----------------------------------------------------
//----------------------------------------------------
// SPDX-FileCopyrightText: Mehul Arvind Prajapati, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

module test_sv_sva_improper_use_system_task;
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

  a_ap_bad: assert property (@(posedge clk) req |=> !req) else $fatal("SVA failed");
  

  /*initial begin
    $dumpfile("dump.vcd");
    $dumpvars(1, test_sv_sva_improper_use_system_task);
  end*/
endmodule: test_sv_sva_improper_use_system_task