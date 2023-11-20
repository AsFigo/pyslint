
    package action_pkg;
        timeunit 1ns;    timeprecision 100ps;                         
        int total_sva_violations = 0;
        task report_sva_violation (string user_defined_err_msg = "Error in SVA");
           $display ("%0t SVA_VIOLATION: %m %s ERR_COUNT: %0d", 
           $time, user_defined_err_msg,
           total_sva_violations);
           total_sva_violations ++;
        endtask : report_sva_violation
     endpackage : action_pkg
     module prop_seq;
        timeunit 1ns;
        timeprecision 1ns;
        import action_pkg::*;
        logic a, b, c;
       logic clk;
       logic ended_sig;
       clocking ck2 @ (posedge clk);   endclocking
       default clocking ck2;   
        //default clocking @ (posedge clk); endclocking
       // Clock 
       initial begin
	a = 0;
	b = 0;
	c = 0;
	clk = 1'b1;
	forever #10 clk = ~clk;
       end
      sequence qA23B;
      // @ (posedge clk) first_match( ##[2:3] b);
      ( ##[2:3] b);  
      endsequence : qA23B
      property test_need_1stmatch(seq, c=1);   // sim ok 
      seq |-> c; 
      endproperty : test_need_1stmatch
      property p (max); 
      //a ##[1:max] b |-> c;//CVC change commented & added succeeding line 
      a ##[0:max] b |-> c; 
     endproperty : p
     apP : assert property(p($)); 
     prop_seqtest: assert property (test_need_1stmatch(qA23B, c)) else
      report_sva_violation();
     prop_seqtest_same : assert property (test_need_1stmatch(qA23B, c)) else 
     report_sva_violation();
      initial begin : test
	int i;
	for (i=1; i<=5; i=i+1) begin
	  ##1; 
	end
         a <= 1'b1; b <= 1'b0; c <= 1'b0;
         ##1;
         a <= 1'b0; b <= 1'b1; c <= 1'b1;
         ##1;
         a <= 1'b0; b <= 1'b1; c <= 1'b0;
         ##1;
         // FAILURE
         a <= 1'b1; b <= 1'b0; c <= 1'b0;
         ##1;
         $finish;
       end
 
    endmodule : prop_seq  
