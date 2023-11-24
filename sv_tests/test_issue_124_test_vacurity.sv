
module test_vacuity;
    bit clk,  a, b, c, d, rst=0;
    int count_of_ap_vac_not_false = 0;
    initial forever #10 clk=!clk; 
    default clocking cb_clk @ (posedge clk);       
    endclocking 
    property vac_true;
        1'b0 |-> 1'b1; 
    endproperty : vac_true
    ap_vac_true: assert property(vac_true);
    ap_vac_false: assert property(not(vac_true));
    ap_vac_not_false: assert property(not(not(vac_true))) count_of_ap_vac_not_false++;
    ap_reject_on: assert property(reject_on(1'b1) 1'b1);  
      
      
      
      initial begin
        a = 0;
        b = 0;
        c = 0;
        d = 0;
        rst = 0;
         a <= 1'b0;
         b <= 1'b1;
         c <= 1'b1;
         d <= 1'b1;


        ##1; $finish;
    end

      
     
        
endmodule : test_vacuity

 
