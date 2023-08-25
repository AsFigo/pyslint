typedef enum bit [1:0]  {RED,BLUE,GREEN,YELLOW} colours_1 ;
typedef enum bit {Rd,WR} eight;

module unused_typedef_f;
   initial
    begin
      //eight a1;//unused typedef but it was defined outside the module

      colours_1 ch1;

      ch1 = RED;

      $display("ch1:%0d",ch1);
     end
endmodule