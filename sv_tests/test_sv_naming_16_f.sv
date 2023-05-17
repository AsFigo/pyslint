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
    // BAD missing end label
    // TBD
  endproperty 

  a_p_good_name : assert property (@(posedge clk) p_good_name)
   else $error ("Fail AB");

endmodule : sva_m

