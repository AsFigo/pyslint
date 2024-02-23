    module an_an_co; 
      timeunit 1ns;
      timeprecision 1ns;

      logic clk=1, a=0, b=0, c=0;

      ap_an_an_co: assert property(@ (posedge clk) 
             a[*1:2] |-> ##[1:3] b |=> c[*1:2]);

      am_an_an_co: assume property(@ (posedge clk) 
             a[*1:2] |-> ##[1:3] b |=> c[*1:2]);

      ap_an_an_coFM: assert property(@ (posedge clk) 
             first_match(a[*1:2]) |-> 
                   first_match(##[1:3] b) |=> c[*1:2]);   

      initial forever #5 clk = !clk; 
      default clocking @(negedge clk); endclocking

      initial begin 

           a<= 1'b1; b <=1'b0; c<= 1'b0;
           ##1;a<= 1'b1; b <=1'b1; c<= 1'b0;
           ##1;a<= 1'b0; b <=1'b0; c<= 1'b1;
           ##1;a<= 1'b0; b <=1'b0; c<= 1'b1;
           repeat (3) ##1; 

          ##1;a<= 1'b1; b <=1'b0; c<= 1'b0;
          ##1;a<= 1'b1; b <=1'b0; c<= 1'b0;
          ##1;a<= 1'b0; b <=1'b0; c<= 1'b0;							 
          repeat (5) ##1;

         a<= 1'b1; b <=1'b0; c<= 1'b0;
         ##1;a<= 1'b1; b <=1'b1; c<= 1'b0;
         ##1;a<= 1'b0; b <=3'b0; c<= 1'b1;
         ##1;a<= 1'b0; b <=1'b0; c<= 1'b0;
         a<= 1'b1; b <=1'b1; c<= 1'b1;
         repeat (3) ##1;

      $display("end of simulation");
      $finish;
  
     end 
 
    endmodule : an_an_co