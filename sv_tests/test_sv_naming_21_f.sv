//----------------------------------------------------
//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

class ex_c;
  function new ();
  endfunction : new
  // BAD - use extern method
  function void should_have_been_extern();
  endfunction : should_have_been_extern
endclass : ex_c

