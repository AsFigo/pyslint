// https://verificationacademy.com/forums/systemverilog/memory-read-showing-xxx-values-apb-verification#reply-117165

module m;
  bit pclk;
  bit psel, penb;

task good();
  @(negedge pclk);
endtask : good

task Write();
begin
  @(negedge pclk) begin 
    psel = 1;
    penb = 0;
    for (int i = 0; i < 64; i=i+1) begin
      @(negedge pclk) begin 
        penb = 1 ;
      end
    end
  end
end
endtask

endmodule

