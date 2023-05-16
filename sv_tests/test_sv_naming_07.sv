//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module cg_wrap_m;
  bit var1;

  covergroup cg_good_name;
    cp_good : coverpoint var1;
  endgroup : cg_good_name
endmodule : cg_wrap_m

