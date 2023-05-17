//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  // BAD - avoid using PASS action block in SVA
  // It usually leads to too many vacuous prints
  a_var1 : assert property (@(posedge clk) var1)
    begin : pass_ab
      $info ("Pass Action Block");
    end : pass_ab
   else $error ("Fail AB");

endmodule : sva_m

