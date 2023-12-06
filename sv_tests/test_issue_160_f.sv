module m;
  
  bit b1;

  task t1_bad();
  begin
    b1 = 0;
  end
  endtask : t1_bad

  task t1();
    b1 = 1;
    #100;
    b1 = 0;
    #100;
  endtask : t1

  function good_f ();
    $display ("No extra begin..end");
    $display ("In SV, no begin..end needed even for multiple line functions");
  endfunction : good_f 

  function bad_f ();
  begin
    $display ("Redundnant begin..end");
    $display ("In SV, no begin..end needed even for multiple line functions");
  end
  endfunction : bad_f 

endmodule : m
