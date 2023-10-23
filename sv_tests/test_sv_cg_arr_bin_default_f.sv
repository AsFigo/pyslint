class ex_c
  bit [31:0] i;

  covergroup cg_with_arr_def;
    coverpoint i {
      bins b_zero = { 0 };
      bins b_small = { [1:100] };
      bins b_100s[5] = {200, 300, 400, 500, 600,
        700};
      bins b_large_vals = { [1001:$] };
      ignore_bins b_ignore = { [701:999] };
      bins others[] = default;
  }
  endgroup

endclass : ex_c

