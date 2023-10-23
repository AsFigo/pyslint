//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


class ex_c;
  bit [7:0] o_sig_8b;


  bit and_c, and_in_a, and_in_b;


  covergroup cg_o_sig;
    cpt_osig : coverpoint (o_sig_8b);
    cr_osig_a : cross cpt_osig, and_in_a;
    // COMPAT_CG_OPT_PI_CL
    type_option.per_instance = 1;
  endgroup : cg_o_sig 

endclass : ex_c

