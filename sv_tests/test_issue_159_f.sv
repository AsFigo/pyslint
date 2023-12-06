module x;
  integer x1;

  function  bad_fn (integer a[], ref ab);
    $display ("%p", a);
  endfunction
 
  function  ok_fn (integer a[]);
    $display ("%p", a);
  endfunction
 
  function  func (ref integer a[]);
    $display ("%p", a);
  endfunction
 
  function automatic auto_func (ref integer a[]);
    $display ("%p", a);
  endfunction
 
  initial begin
    integer a [];
    a = {1,2,3,4,5};
    x1=func(a);
  end
endmodule 
