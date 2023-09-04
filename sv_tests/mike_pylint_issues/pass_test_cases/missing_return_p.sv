module missing_return_p;
    int x;

  //function to add two integer numbers.
  function int sum(input int a,b);
      sum = a+b;//a+b is assigned to the name of the function itself
  endfunction

  initial begin
    x=sum(10,5);
    $display("\tValue of x = %0d",x);
  end
endmodule