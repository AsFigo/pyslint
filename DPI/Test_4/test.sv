module m();
export "DPI-C" c_exported_func = function func;
import "DPI-C" pure function int cfunc (input int a ,b);
/*This function can be called from both SV or C side. */
function int func(input int x, y);
begin
func = x + y;
end
endfunction
int z;
initial
begin
#5;
z = cfunc(2, 3);
if(z == 5)
$display("PASSED");
else
$display("FAILED");
end
endmodule
