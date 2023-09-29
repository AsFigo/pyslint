module af_sv_dpi_openarr;
  import "DPI-C" function integer c_sum(input bit [31:0] input_array[]);
   
   initial begin
     bit [31:0] data[4] = {11, 22, 33, 44};
      int result;
      
      // Call the DPI function
      result = c_sum(data);
      
      $display("Sum of array elements: %d", result);
   end
endmodule : af_sv_dpi_openarr

