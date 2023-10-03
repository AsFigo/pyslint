//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan,
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  // BAD - unnamed SVA
  assert property (@(posedge clk) var1)
    else $error ("Bad style - unnamed SVA");

endmodule : sva_m

