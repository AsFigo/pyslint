//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan,
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  // BAD - wrong prefix SVA
  bad_sva_label : assert property (@(posedge clk) var1)
    else $error ("Bad style - wrong prefix in SVA");

endmodule : sva_m

