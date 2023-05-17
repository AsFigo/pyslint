//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sva_m;
  bit var1;
  bit clk;

  property p_good_name;
    var1;
  endproperty : p_good_name

  a_p_good_name : assert property (@(posedge clk) p_good_name)
   else $error ("Fail AB");

endmodule : sva_m

