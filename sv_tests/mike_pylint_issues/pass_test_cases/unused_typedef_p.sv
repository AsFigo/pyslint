//unused typedef 
typedef enum bit [1:0]  {RED,BLUE,GREEN,YELLOW} colours_1 ;
typedef enum bit {RD,WR} eight;

module unused_typedef_p;
   initial
    begin

     eight a1;//used the typedef declared outside the module
     colours_1 ch1;

     ch1 = RED;
     $display("ch1:%0d",ch1);

     a1 = WR;
     $display("a1:%0d",a1);

end

endmodule