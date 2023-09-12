module m();
import "DPI-C" pure function int myFunction1 (); 
import "DPI-C" pure function int myFunction2 ();
integer i, j;
initial
begin
#1;
  i = myFunction1();
  j = myFunction2();
  $display(i, j);
  if( i == 5 && j == 10)
    $display("PASSED");
  else
    $display("FAILED");
end
endmodule
