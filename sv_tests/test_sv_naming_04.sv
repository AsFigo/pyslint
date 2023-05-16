//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


class af_good_c;
  rand int i;

  constraint good_cst {i > 10;}
  constraint bad_name {i > 4;}

endclass : af_good_c
