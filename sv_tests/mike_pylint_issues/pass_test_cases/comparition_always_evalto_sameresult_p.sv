module comparition_always_evalto_sameresult_p;

   // Declare a variable to store the result of the comparisons
   int result = 0;

   // Test the comparisons
   initial begin
      if (1 == 1) begin
         result = 1;//compartion always evaluate to same result
         $display("value result:%0d",result);
      end
      if (1 != 0) begin
         result = 1;//compartion always evaluate to same result
          $display("value result:%0d",result);
      end
   end

endmodule