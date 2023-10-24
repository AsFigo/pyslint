//----------------------------------------------------
// SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

class fruits_c;

  string fruits[*];

  function void disp ();
    fruits["apple"] = "red";
    fruits["banana"] = "yellow";
    fruits["cherry"] = "red";

    // Using wildcard index, which is not recommended
    /*
    foreach (fruits[key])
      $display("Fruit: %s, Color: %s", key, fruits[key]);
    */
    $display ("%p", fruits);
    $display ("%s", fruits["apple"]);
  endfunction : disp

endclass: fruits_c

module top;
  fruits_c f_0;

  initial begin
    f_0 = new();
    f_0.disp();
    $finish (2);
  end
endmodule : top


