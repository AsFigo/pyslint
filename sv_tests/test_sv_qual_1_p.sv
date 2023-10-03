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

  assign sample_w = 1'b0;

  always_comb begin : alw_c
    and_c = and_in_a && and_in_b;
  end : alw_c

  initial begin : init_blk
    $timeformat (-9, 3, " ns", 5);
  end : init_blk


  // Sample one line comment

  sequence s_a_b;
    @(posedge clk) and_in_a ##10 and_in_b;
  endsequence : s_a_b

  property p_good_name;
    var1 |=> s_a_b;
  endproperty : p_good_name

  /* Multi-line comment
  * Second line
  * Third line
  */

  a_p_good_name : assert property (@(posedge clk) p_good_name)
   else $error ("Fail AB");
  
  m_oneh_inp : assume property (@(posedge clk) $onehot0 (sig_4b));
  c_inp : cover property (@(posedge clk) (sig_4b == 4'b0010));

endmodule : sv_qual

