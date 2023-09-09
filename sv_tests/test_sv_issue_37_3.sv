class data;
  rand bit [15:0] field1;
  constraint c_f1 { field1 dist {[0:31] := 1, [32:65535] := 1};}
endclass

module testbench;
   
  initial begin
    data test_h;
    test_h = new();
    
    repeat(10) begin
        assert(test_h.randomize());
        $display("field1 = %h", test_h.field1);
    end
  end

endmodule
