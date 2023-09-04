//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------


module sv_qual (input bit clk, rst_n, 
  input [3:0] sig_4b,
  output [7:0] o_sig_8b);

  bit var1;

  wire sample_w;
  logic and_c, and_in_a, and_in_b;


  covergroup cg_o_sig @(posedge clk);
    cpt_osig : coverpoint (o_sig_8b);
    cr_osig_a : cross cpt_osig, and_in_a;
  endgroup : cg_o_sig 

endmodule : sv_qual

