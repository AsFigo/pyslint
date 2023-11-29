module tb;
int pass1, fail1; 
bit clk , a , b ;
 
always #5 clk = !clk;
     

  assert property(
    @(posedge clk) a |-> b[->0]) begin 
   pass1=pass1+1; $display("T:%0t OK Pass",$time); end  
   else begin  $display("T:%0t OK Fails",$time); fail1=fail1+1; end    
 
  initial begin  
    $dumpfile("dump.vcd"); $dumpvars;
      #4; a = 1;
 #10; a = 0;
 
 #30; b = 1;
    #25; $finish();
  end  
endmodule 
