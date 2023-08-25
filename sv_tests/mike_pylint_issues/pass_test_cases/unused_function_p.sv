module unused_function_p;

 initial begin

    x(); //function x used
    y(); //function y  used

 end
function void x;
   //function definition
endfunction

function void y;
 //function definition
endfunction

endmodule