//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan,
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  property bad_name;
    var1;
  endproperty : bad_name

  a_var1 : assert property (@(posedge clk) bad_name)
   else $error ("Fail AB");

endmodule : sva_m

