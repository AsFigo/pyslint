//----------------------------------------------------
//----------------------------------------------------
// SPDX-FileCopyrightText: Mehul Arvind Prajapati, 
//                         AsFigo Technologies, UK
// SPDX-License-Identifier: MIT
//----------------------------------------------------

module test_sva_m; 
    timeunit 1ns;
    timeprecision 1ns;
    logic clk=0, a, b, c;

    a_1: assert property(@ (posedge clk) 
                    c |-> a[->0] ##0 b);
    
    a_2: assert property(@ (posedge clk)
                     a[*0] ##0 b |-> c);
					 
    a_3: assert property(@ (posedge clk) 
                    1 intersect 1[*2] |=> c);
    
    initial forever #5 clk = ~clk;
      
    initial begin  
     #10;
     c = 1'b1;
     a = 1'b0;
     #10 a = 1'b1;
     #20;

    $stop;
    end
      
      /* initial begin
        $dumpfile("dump.vcd");
        $dumpvars(1,test_sva_m);
      end */

endmodule : test_sva_m
