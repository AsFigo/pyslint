//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


class ex_c;
  bit [7:0] o_sig_8b;


  bit and_c, and_in_a, and_in_b;


  covergroup cg_o_sig;
    cpt_and_c : coverpoint and_c;
    cpt_osig : coverpoint o_sig_8b {
      bins useful_vals [10] = {[0:200]};
      illegal_bins invalid_vals = {255};
    }
  endgroup : cg_o_sig 

endclass : ex_c

