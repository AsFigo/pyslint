//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan,
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

interface af_sv_if ();
  wire  wire_a;
  logic logic_a;
  bit bad_2st;
  int bad_2st_int;
  bit [7:0] bad_2st_vec;
  bit [3:0] bad_2st_2d [10];
  bit [9:0] bad_2st_3d [10][5];
endinterface : af_sv_if

