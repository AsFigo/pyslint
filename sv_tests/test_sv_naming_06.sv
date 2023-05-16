//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


class cg_wrap_c;
  bit var1;

  covergroup bad_group_name;
    cp_good : coverpoint var1;
  endgroup : bad_group_name
endclass : cg_wrap_c

