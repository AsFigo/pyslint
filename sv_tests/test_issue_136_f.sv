module test;
 
  bit req1,req2;
  bit clk;
 
  always #5 clk=~clk;
 
 
  initial begin
  #100;
    expect (@(posedge clk) 1);
    expect (@(posedge clk) req1);
    expect (@(posedge clk) req1 ##1 1);
    expect(@(posedge clk) req1 ##2 req2) else $error ("expect failure");
    $display("DONE");
end
 
  initial
    begin
      repeat(10)
        begin
            req1=$urandom;
            req2=$urandom;
            #12;
        end
      $finish;
    end
endmodule
