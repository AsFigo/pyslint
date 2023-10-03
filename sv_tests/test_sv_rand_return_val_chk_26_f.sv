//----------------------------------------------------
// SPDX-FileCopyrightText: Jayaraman R P,
//                         Verifworks Pvt Ltd,India
// SPDX-License-Identifier: MIT
//----------------------------------------------------
module randomization_example;

class test_rand;
    rand bit [7:0] data1;
endclass: test_rand

  initial begin
    MyRandomizedClass obj = new(); // Create and randomize an instance of the class
    obj.randomize();
    void'(obj.randomize());        //Not a proper way to randomize
    if (obj.randomize()) begin
      // Randomization successful
      $display("Randomized data1: %h", obj.data1);
    end else begin
      // Randomization failed
      $display("Randomization failed. Constraints may not be satisfied.");
    end
  end
endmodule: randomization_example
