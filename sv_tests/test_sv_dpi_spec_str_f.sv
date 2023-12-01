function void sv_fn_cu();
endfunction : sv_fn_cu

task sv_t_cu();
endtask : sv_t_cu

import "DPI" function int c_sum_cu(input bit [31:0] input_array[]);
export "DPI" function sv_fn_cu;
export "DPI" task sv_t_cu;

module af_sv_dpi_openarr;
  import "DPI" function int c_sum(input bit [31:0] input_array[]);
   
   initial begin
     bit [31:0] data[4] = {11, 22, 33, 44};
      int result;
      
      // Call the DPI function
      result = c_sum(data);
      
      $display("Sum of array elements: %d", result);
   end
endmodule : af_sv_dpi_openarr

