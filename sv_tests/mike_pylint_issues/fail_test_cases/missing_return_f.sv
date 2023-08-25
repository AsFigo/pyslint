module missing_return_f;
  //function to add two integer numbers.
  function int sum(input int a,b);
      sum = a+b;
  endfunction

  initial begin

          sum(10,5);//while calling the function must assigned to the int variabe.
  end
endmodule