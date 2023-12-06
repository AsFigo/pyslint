//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

interface af_sv_if ();
  logic bit_a;

  logic clk;

  clocking cb @(posedge clk);
  endclocking : cb 
endinterface : af_sv_if

