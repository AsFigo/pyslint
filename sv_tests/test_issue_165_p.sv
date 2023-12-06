//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

`define VERILATOR
interface af_sv_if ();
  logic bit_a;

  logic clk;

  `ifndef VERILATOR
  clocking cb @(posedge clk);
  endclocking : cb 
  `endif // VERILATOR
endinterface : af_sv_if

