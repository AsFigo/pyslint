module t;
  logic clk=0, a, req, ack; 
  int data, addr, max_sig, max_count=10;
 
  default clocking cb_clk @ (posedge clk);
  endclocking
 
  sequence q_test ( 
            local input int lv_count=0,   
            int max = max_sig,
            int data=lv_count); 

            int v_ct = lv_count  - max;    
            (a, lv_count+= 1, v_ct += lv_count) ##[1:40] (addr==lv_count || v_ct ==0 || data==0);
  endsequence : q_test
  ap_q_test: assert property(q_test);

  initial max_count=10;

  property q_req_ack;  
           int v_count=0;  // initialize v_count
           $rose(req) |-> (1'b1, v_count+= 1) [*0:$] ##1  v_count >= max_count || ack;
  endproperty  : q_req_ack
  a_q_req_ack : assert property (q_req_ack);
      
  initial forever #1 clk = !clk; 

  initial 
    begin
	    $display("Pass Case Scenario:");
	    addr = 1;
	    req = 0;
	    a = 1;
	    data = 0;
	    ack = 0;
	    ##1;
	    req = 1'b1; ack = 1'b1;  data=1; addr=0;   
	    #10 $finish;
    end 
endmodule : t 
