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

  // BAD label should have c_ as prefix for cover
  wrong_label : cover property (@(posedge clk) p_good_name);

endmodule : sva_m

