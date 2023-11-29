module tb;
int pass1, fail1; 
bit clk , a , b ;
 
always #5 clk = !clk;
     
  assert property(@(posedge clk) b[->0] |-> a);

 
  initial begin  
    $dumpfile("dump.vcd"); $dumpvars;
      #4; a = 1;
 #10; a = 0;
 
 #30; b = 1;
    #25; $finish();
  end  
endmodule 
