package pack1;
  import "DPI-C" function int good_dpi_f(input int v, output int o);
  import "DPI-C" function int bad_dpi_f_4st(input integer v, output logic o);
  import "DPI-C" function int bad_dpi_f_4st_da(input int dyn_a[$][]);
endpackage
/*-- ---*/
module mymodule();
int i, j;
int o1 ,o2, o3;
initial
begin
  #1;
  j = 10;
  o3 =pack1:: myFunction1(j, o1);//should be 10/2 = 5
  pack1::myFunction2(j, 2+3, o2); // 5 += 10 + 2+3
  $display(o1, o2);
  if( o1 == 5 && o2 == 15)
    $display("PASSED");
  else
    $display("FAILED");
end
endmodule

