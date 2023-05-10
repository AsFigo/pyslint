
interface af_sv_if ();
  wire  wire_a;
  logic logic_a;
endinterface : af_sv_if


interface af_sv_intf_bad ();
endinterface : af_sv_intf_bad

class af_bad_class_name;
endclass : af_bad_class_name

class af_good_c;
  rand int i;

  constraint good_cst {i > 10;}
  constraint bad_name {i > 4;}

endclass : af_good_c
module af_good_m;
endmodule : af_good_m

module af_bad_mod_name;
endmodule : af_bad_mod_name

