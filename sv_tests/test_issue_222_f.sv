
// BAD code - pure task is not allowed
// but some tools compile
 import "DPI-C" pure task bad_pure_dpi_t (logic [3:0] a);
 import "DPI-C" pure task normal_dpi_t (logic [3:0] a);

module top ;
endmodule
