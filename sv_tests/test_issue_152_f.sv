module m;
  import "DPI-C" function int bad_dpi_f_mda(input int dyn_a[][]);
  import "DPI-C" function int ok_dpi_f_dyn_arr(input int dyn_a[]);
  import "DPI-C" task bad_dpi_t_mda(input int dyn_a[][]);
endmodule

