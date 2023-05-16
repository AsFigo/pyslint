//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


class cg_wrap_c;
  bit var1;

  covergroup cg_good_name;
    cp_good : coverpoint var1;
  endgroup : cg_good_name
endclass : cg_wrap_c

