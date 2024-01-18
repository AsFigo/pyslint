class bli_c;
  bit foo_sel;
  bit impl_foo;
  
  rand int foo;
  
  constraint cst_ok {
    foo == (foo_sel ? 5 :6);
  }
  
  constraint cst_ok_impl {
    impl_foo -> (foo_sel) ? 5 :6;
  }
  
  constraint cst_bad {
    foo == (foo_sel) ? 5 :6;
  }
  
  function void post_randomize();
    $display ("%p", this);
  endfunction
endclass

module m;
  bli_c u_bli_c_0;
  
  initial begin
    u_bli_c_0 = new();
    repeat (5) u_bli_c_0.randomize(); 
    #10;
    $finish (2);
  end
endmodule
