module unused_function_f;

 initial begin

    x(); //function declaration
    //y();function y not used

 end
function void x;
   //function definition
endfunction

function void y;
 //function definition
endfunction

endmodule