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

endmodule : m
