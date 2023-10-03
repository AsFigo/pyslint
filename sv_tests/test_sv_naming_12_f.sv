//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan,
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  // BAD - missing FAIL action block in SVA
  a_var1 : assert property (@(posedge clk) var1);

endmodule : sva_m

